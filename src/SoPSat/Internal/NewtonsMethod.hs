module SoPSat.Internal.NewtonsMethod
where

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromJust)

import SoPSat.SoP (atoms)
import SoPSat.Internal.SoP
  (Atom(..), Symbol(..), Product(..), SoP(..))


-- | Evaluates SoP given atom bindings
evalSoP :: (Ord f, Ord c, Floating n)
        => SoP f c
        -- ^ Expression to evaluate
        -> Map (Atom f c) n
        -- ^ Bindings from atoms to values
        -> n
        -- ^ Evaluation result
evalSoP (S []) _ = 0
evalSoP (S ps) binds = sum $ map (`evalProduct` binds) ps


-- | Evaluates product given atom bindings
--
-- Used by @evalSoP@
evalProduct :: (Ord f, Ord c, Floating n)
            => Product f c
            -- ^ Product to evalute
            -> Map (Atom f c) n
            -- ^ Atom bindings
            -> n
            -- ^ Evaluation results
evalProduct (P ss) binds = product $ map (`evalSymbol` binds) ss

-- | Evaluates symbol given atom bindings
--
-- Used by @evalProduct@
evalSymbol :: (Ord f, Ord c, Floating n)
           => Symbol f c
           -- ^ Symbol to evaluate
           -> Map (Atom f c) n
           -- ^ Atom bindings
           -> n
           -- ^ Evaluation result
evalSymbol (I i) _     = fromInteger i
evalSymbol (A a) binds = f $ M.lookup a binds
  where f (Just n) = n
        f Nothing  = 0
evalSymbol (E b p) binds = exp (evalProduct p binds * log (evalSoP b binds))

-- | Analitically computes derivative of an expression
-- with respect to an atom
--
-- Returns function similar to @evalSoP@
derivative :: (Ord f, Ord c, Floating n)
           => SoP f c
           -- ^ Expression to take a derivative of
           -> Atom f c
           -- ^ Atom to take a derivetive with respect to
           -> (Map (Atom f c) n -> n)
           -- ^ Function from bindings, representing point,
           -- to value of the derivative at that point           
derivative sop symb = \binds -> sum $ d <*> [binds]
  where d = map (`derivativeProduct` symb) $ unS sop

-- | Analitically computes derivative of a product
-- with respect to an atom
--
-- Used by @derivative@
derivativeProduct :: (Ord f, Ord c, Floating n)
                  => Product f c
                  -- ^ Product to take a derivative of
                  -> Atom f c
                  -- ^ Atom to take a derivative with respect to
                  -> (Map (Atom f c) n -> n)
                  -- ^ Function from bindings to a value
derivativeProduct (P [])     _ = const 0
derivativeProduct (P (s:ss)) symb = \binds -> derivativeSymbol s symb binds * evalProduct ps binds + evalSymbol s binds * derivativeProduct ps symb binds
  where ps = P ss

-- | Analitically computes derivative of a symbol
-- with respect to an atom
--
-- Used by @derivativeProduct@
derivativeSymbol :: (Ord f, Ord c, Floating n)
                 => Symbol f c
                 -- ^ Symbol to take a derivate of
                 -> Atom f c
                 -- ^ Atom to take a derivate with respect to
                 -> (Map (Atom f c) n -> n)
                 -- ^ Function from bindings to a value
derivativeSymbol (I _) _ = const 0
derivativeSymbol (A a) atom
  | a == atom = const 1
  | otherwise = const 0
derivativeSymbol e@(E b p) atom = \binds ->
    expExpr binds *
    (derivative b atom binds * evalProduct p binds
      / evalSoP b binds
      + logExpr binds
      * derivativeProduct p atom binds)
  where expExpr = evalSymbol e
        logExpr = log. evalSoP b

-- | Finds if an expression can be equal to zero
newtonMethod :: (Ord f, Ord c, Ord n, Floating n)
             => SoP f c
             -- ^ Expression to check
             -> Either (Map (Atom f c) n) (Map (Atom f c) n)
             -- ^ @Right binds@ - Atom bindings when expression is equal to zero
             --   @Left binds@ - Last checked bindings
newtonMethod sop = go init_guess steps
  where
    consts     = atoms sop
    derivs     = M.fromSet (derivative sop) consts
    init_guess = M.fromSet (const 10) consts
    steps = 40

    go guess 0 = Left guess
    go guess n
      | val <= 0.1 = Right guess
      | otherwise =
        let
          new_guess = foldl (\binds (c,x) -> M.insert c (x - val / dsdc c) binds) guess $ M.toList guess
        in go new_guess (n - 1)
      where
        val = evalSoP sop guess
        dsdc c = fromJust (M.lookup c derivs) guess
