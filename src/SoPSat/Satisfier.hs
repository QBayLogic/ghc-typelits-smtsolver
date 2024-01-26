{-# LANGUAGE RecordWildCards #-}

module SoPSat.Satisfier
  ( -- * State
    SolverState
    -- * State manipulation
  , declare
  , assert
  , unify
    -- * State information
  , range
  , ranges
    -- * State execution
  , withState
  , runStatements
  , evalStatements
    -- * Expressions
  , evalSoP
  )
where

import Control.Applicative ((<|>))
import Control.Arrow       (second)
import Control.Monad       (when, (>=>), unless)

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (isNothing)

import SoPSat.SoP
import SoPSat.Internal.SoP
  (Atom(..), Symbol(..), Product(..), SoP(..))
import SoPSat.Internal.Unify
import SoPSat.Internal.Range
import SoPSat.Internal.NewtonsMethod
import SoPSat.Internal.SolverMonad


parts :: [a] -> [[a]]
parts [] = []
parts (x:xs) = xs : map (x:) (parts xs)


-- | Declares atom in the state
-- ignores constants and only declare function arguments
declareAtom :: (Ord f, Ord c) => Atom f c -> SolverState f c Bool
declareAtom (C _) = return True
declareAtom (F _ args) = and <$> mapM declareSoP args

-- | Declares symbol in the state with the default interval
-- If symbol exists preserves the old interval
declareSymbol :: (Ord f, Ord c) => Symbol f c -> SolverState f c Bool
declareSymbol (I _) = return True
declareSymbol (A a) = do
  ranges <- getRanges
  when (isNothing (M.lookup a ranges)) (putRange a range)
  declareAtom a
  where
    range = Range (Bound (int 0)) Inf
declareSymbol (E b p) = (&&) <$> declareSoP b <*> declareProduct p

-- | Similar to @declareSoP@ but for @Product@
declareProduct :: (Ord f, Ord c) => Product f c -> SolverState f c Bool
declareProduct = fmap and . mapM declareSymbol . unP

-- | Declare SoP in the state with default values
-- Creates range for free-variables
declareSoP :: (Ord f, Ord c) => SoP f c -> SolverState f c Bool
declareSoP s@(S ps)
  | left /= int 0 = (&&) <$> (and <$> mapM declareProduct ps) <*> assert (SoPE left right LeR)
  | otherwise = and <$> mapM declareProduct ps
  where
    (left, right) = splitSoP (int 0) s

-- | Declare expression to state, returns normalised expression
--
-- Common for @declare@, @assert@, and @unify@
declareToState :: (Ord f, Ord c) => SoPE f c -> SolverState f c (SoPE f c)
declareToState SoPE{..} = do
  r1 <- declareSoP lhs
  r2 <- declareSoP rhs
  us <- getUnifiers
  let
    lhs' = substsSoP us lhs
    rhs' = substsSoP us rhs
  unless (r1 && r2) (fail "")
  return (SoPE lhs' rhs' op)


-- | Declare equality of two expressions
-- Adds new unifiers to the state
declareEq :: (Ord f, Ord c)
          => SoP f c
          -- ^ First expression
          -> SoP f c
          -- ^ Second expression
          -> SolverState f c Bool
          -- ^ Similar to @declare@ but handles only equalities
declareEq u v =
  do
    (Range low1 up1) <- getRangeSoP u
    (Range low2 up2) <- getRangeSoP v
    lowRes <- boundComp low1 low2
    upRes <- boundComp up1 up2

    -- Declaration and assertions of expression is done on the whole domain
    -- if two expressions are equal, their domains will intersect
    --
    -- g(x) in [1,5] and forall x  g(x) = f(x) then f(x) in [1,5]
    lowerUpdate <-
      case (lowRes,low1,low2) of
        (True,_,Bound lowB2) -> propagateInEqSoP u GeR lowB2
        (False,Bound lowB1,_) -> propagateInEqSoP v GeR lowB1
        (_,_,_) -> return True

    upperUpdate <-
      case (upRes,up1,up2) of
        (True,_,Bound upB2) -> propagateInEqSoP u LeR upB2
        (False,Bound upB1,_) -> propagateInEqSoP v LeR upB1
        (_,_,_) -> return True
    
    declareEq' u v
    return (lowerUpdate && upperUpdate)
  where
    boundComp Inf _ = return False
    boundComp _ Inf = return True
    boundComp (Bound a) (Bound b) = assert (SoPE a b LeR)

declareEq' :: (Ord f, Ord c) => SoP f c -> SoP f c -> SolverState f c ()
declareEq' (S [P [A a]]) v = putUnifiers [Subst a v]
declareEq' u (S [P [A a]]) = putUnifiers [Subst a u]
declareEq' u v = putUnifiers $ unifiers u v


-- | Updates interval information for a symbol
propagateInEqSymbol :: (Ord f, Ord c)
                    => Symbol f c
                    -- ^ Updated symbol
                    -> OrdRel
                    -- ^ Relationship between the symbol and target
                    -> SoP f c
                    -- ^ Target Boundary
                    -> SolverState f c Bool
                    -- ^ Similat to @declareInEq@
propagateInEqSymbol (I _) _ _ =
  return True -- No need to update numbers
propagateInEqSymbol (A a) rel bound = do
  (Range low up) <- getRange a
  -- New bound is less/greater than the old one
  -- The check is done before propagation
  -- This assumption is potentially wrong
  case rel of
    LeR
      -> putRange a (Range low rangeBound)
    GeR
      -> putRange a (Range rangeBound up)
    EqR -> error "propagateInEqSymbol:EqR: unreachable"
  return True
  where
    rangeBound = Bound bound
propagateInEqSymbol (E b (P [I i])) rel (S [P [I j]])
  | (Just p) <- integerRt i j
  = propagateInEqSoP b rel (int p)
propagateInEqSymbol (E (S [P [I i]]) p) rel (S [P [I j]])
  | (Just e) <- integerLogBase i j
  = propagateInEqProduct p rel (int e)
propagateInEqSymbol _ _ _ = fail ""

-- | Propagates interval information down the Product
propagateInEqProduct :: (Ord f, Ord c)
                     => Product f c
                     -- ^ Updates expression
                     -> OrdRel
                     -- ^ Relationship between the expression and target
                     -> SoP f c
                     -- ^ Target boundary
                     -> SolverState f c Bool
                     -- ^ Similar to @declareInEq@
propagateInEqProduct (P [symb]) rel target_bound = propagateInEqSymbol symb rel target_bound
propagateInEqProduct (P ss) rel target_bound =
  and <$> mapM (uncurry propagate) (zipWith (curry (second P)) ss (parts ss))
  where
    -- a <= x * y => a/y <= x and a/x <= y
    -- Currently simply propagating the bound further
    -- a <= x * y => a <= x and a <= y
    propagate symb _prod = propagateInEqSymbol
                          symb rel
                          target_bound
                          -- (target_bound |/| prod)

-- | Propagates interval information down the SoP
propagateInEqSoP :: (Ord f, Ord c)
                 => SoP f c
                 -- ^ Updated expression
                 -> OrdRel
                 -- ^ Relationship between the expression and target
                 -> SoP f c
                 -- ^ Target boundary
                 -> SolverState f c Bool
                 -- ^ Similar to @declareInEq@
propagateInEqSoP (S [P [symb]]) rel target_bound = propagateInEqSymbol symb rel target_bound
propagateInEqSoP (S ps) rel target_bound =
  and <$> mapM (uncurry propagate) (zipWith (curry (second S)) ps (parts ps))
  where
    -- a <= x + y => a - y <= x and a - x <= y
    propagate prod sm = propagateInEqProduct
                        prod rel
                        (target_bound |-| sm)

-- | Declare inequality of two expressions
-- Updates interval information in the state
declareInEq :: (Ord f, Ord c)
            => OrdRel
            -- ^ Relationship between expressions
            -> SoP f c
            -- ^ Left-hand side expression
            -> SoP f c
            -- ^ Right-hand side expression
            -> SolverState f c Bool
            -- ^ Similar to @declare@ but handles only inequalities
declareInEq EqR u v = declareEq u v >> return True
declareInEq op u v =
    let
      (u', v') = splitSoP u v
    -- If inequality holds with current interval information
    -- then no need to update it
    in do
      res <- assert (SoPE u' v' op)
      if res then return True
        else let
          op1 = op
          op2 = opposite op1
        in (&&) <$> propagateInEqSoP u' op v' <*> propagateInEqSoP v' op2 u'
    where
      opposite LeR = GeR
      opposite GeR = LeR
  
-- | Declare expression to the state
declare :: (Ord f, Ord c)
        => SoPE f c
        -- ^ Expression to declare
        -> SolverState f c Bool
        -- ^ - True - if expression was declared
        --   - False - if expression contradicts current state
        --
        -- State will become @Nothing@ if it cannot reason about these kind of expressions
declare = declareToState >=> \SoPE{..} ->
  case op of
    EqR -> declareEq lhs rhs
    _   -> declareInEq op lhs rhs

-- | Assert that two expressions are equal using unifiers from the state
assertEq :: (Ord f, Ord c)
         => SoP f c
         -- ^ Left-hand side expression
         -> SoP f c
         -- ^ Right-hand size expression
         -> SolverState f c Bool
         -- ^ Similar to assert but only checks for equality @lhs = rhs@
assertEq lhs rhs = return (lhs == rhs)

-- | Assert using only ranges stores in the state
assertRange :: (Ord f, Ord c)
            => SoP f c
            -- ^ Left-hand side expression
            -> SoP f c
            -- ^ Right-hand size expression
            -> SolverState f c Bool
            -- ^ Similar to @assert@ but uses only intervals from the state to check @lhs <= rhs@
assertRange lhs rhs = uncurry assertRange' $ splitSoP lhs rhs

assertRange' :: (Ord f, Ord c) => SoP f c -> SoP f c -> SolverState f c Bool
assertRange' (S [P [I i]]) (S [P [I j]]) = return (i <= j)
assertRange' lhs rhs = do
  (Range _ up1) <- getRangeSoP lhs
  (Range low2 up2) <- getRangeSoP rhs
  -- If both sides increase infinitely, fail to use Newton's method
  -- Information about rate of growth is required
  -- to check inequality on the whole domain
  if up1 == up2 && up2 == Inf then fail ""
    else case (up1,low2) of
           (Inf,_) -> return False
           (_,Inf) -> return False
           (Bound ub1, Bound lb2)
           -- Orders of recursive checks matters
           -- @runLemma2@ in the tests loops indefinitely
           -- possibly other test cases too
             -> do
               r1 <- if ub1 /= lhs then assert (SoPE ub1 rhs LeR)
                                        else return False
               r2 <- if lb2 /= rhs then assert (SoPE lhs lb2 LeR)
                                        else return False
               return (r1 || r2)

-- | Assert using only Newton's method
assertNewton :: (Ord f, Ord c)
             => SoP f c
             -- ^ Left-hand side expression
             -> SoP f c
             -- ^ Right-hand side expression
             -> SolverState f c Bool
             -- ^ Similar to @assert@ but uses only Newton's method to check @lhs <= rhs@
assertNewton lhs rhs =
  let
    expr = rhs |-| lhs |+| int 1
  in checkExpr expr
  where
    -- hasFunction :: (Ord f, Ord c) => SoP f c -> Bool
    -- hasFunction = any isFunction . atoms

    checkExpr :: (Ord f, Ord c) => SoP f c -> SolverState f c Bool
    checkExpr expr
      | (Right binds) <- newtonMethod expr
      = not <$> checkBinds binds
      | otherwise
      = return True

    checkBinds :: (Ord f, Ord c, Ord n, Floating n) => Map (Atom f c) n -> SolverState f c Bool
    checkBinds binds = and <$> mapM (uncurry (checkBind binds)) (M.toList binds)

    checkBind :: (Ord f, Ord c, Ord n, Floating n) => Map (Atom f c) n -> Atom f c -> n -> SolverState f c Bool
    checkBind binds c v = do
      (Range left right) <- getRange c
      return (checkLeft binds v left && checkRight binds v right)

    checkLeft :: (Ord f, Ord c, Ord n, Floating n) => Map (Atom f c) n -> n -> Bound f c -> Bool
    checkLeft _ _ Inf = True
    checkLeft binds v (Bound sop) = evalSoP sop binds <= v

    checkRight :: (Ord f, Ord c, Ord n, Floating n) => Map (Atom f c) n -> n -> Bound f c -> Bool
    checkRight _ _ Inf = True
    checkRight binds v (Bound sop) = v <= evalSoP sop binds

-- | Assert if given expression holds in the current environment
assert :: (Ord f, Ord c)
       => SoPE f c
       -- ^ Asserted expression
       -> SolverState f c Bool
       -- ^ - True - if expressions holds
       --   - False - otherwise
       --
       -- State will become @Nothing@ if it cannot reason about these kind of expressions
assert = declareToState >=> \SoPE{..} ->
  case op of
    EqR -> assertEq lhs rhs
    LeR -> do
      r1 <- assertEq lhs rhs
      if r1 then return True
        else do
        assertRange lhs rhs <|> assertNewton lhs rhs
    GeR -> do
      r1 <- assertEq lhs rhs
      if r1 then return True
        else do
        assertRange rhs lhs <|> assertNewton rhs lhs

-- | Get unifiers for an expression
-- minimal set of expressions that should hold for the expression to hold
unify :: (Ord f, Ord c)
      => SoPE f c
      -- ^ Unified expression
      -> SolverState f c [SoPE f c]
      -- ^ List of unifiers - Minimal list of unifiers for the expression to hold.
      -- The list is empty, if it never holds
      --
      -- State will always be valid after a call
unify = declareToState >=> \expr@SoPE{..} ->
    case op of
      EqR -> return (filter (/= expr) $ map unifier2SoPE (unifiers lhs rhs))
      _ -> return []
  where
    unifier2SoPE Subst{..} = SoPE (symbol sConst) sSoP EqR

-- | Get range of possible values for an expression
range :: (Ord f, Ord c)
      => SoP f c
      -- ^ Expression
      -> SolverState f c (Maybe (SoP f c), Maybe (SoP f c))
      -- ^ (lower bound, upper bound) - Range for an expression
      --
      -- @Nothing@ means that the expression is unbounded
      -- from that side
range sop = do
  _ <- declareSoP sop
  (Range low up) <- getRangeSoP sop
  return (boundSoP low, boundSoP up)

-- | Get list of all ranges stored in a state
ranges :: (Ord f, Ord c)
       => SolverState f c [(Maybe (SoP f c), SoP f c, Maybe (SoP f c))]
       -- ^ (lower bound, symbol, upper bound) - Similar to @range@
       --     but also provides expression
ranges =
  map (\(a,Range low up) -> (boundSoP low, symbol a, boundSoP up)) . M.toList <$> getRanges
