{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}

module SoPSat.SoP
  ( -- * SoP Types
    Atom
  , Symbol
  , Product
  , SoP
  , SoPE (..)
  , ToSoP (..)
    -- * Operators
  , (|+|)
  , (|-|)
  , (|*|)
  , (|/|)
  , (|^|)
    -- * Relations
  , OrdRel(..)
    -- * Related
  , constants
  , atoms
  , int
  , cons
  , symbol
  , func
    -- * Predicates
  , isConst
  , isFunction
  )
where

import Data.List (intercalate)

import Data.Set (Set, union)
import qualified Data.Set as S

import SoPSat.Internal.SoP

-- | Convertable to a sum of products
-- with `f` being type to represent functions
-- and `c` being type to represent constants
class (Ord f, Ord c) => ToSoP f c a where
  toSoP :: a -> SoP f c

-- | Predicate for constant @Atom@s
isConst :: Atom f c -> Bool
isConst (C _) = True
isConst _ = False

-- | Predicate for function @Atom@s
isFunction :: Atom f c -> Bool
isFunction (F _ _) = True
isFunction _ = False


instance (Show f, Show c) => Show (Atom f c) where
  show (C c) = show c
  show (F f args) = show f ++ "(" ++ intercalate ", " (map show args) ++ ")"

instance (Ord f, Ord c) => ToSoP f c (Symbol f c) where
  toSoP s = simplifySoP $ S [P [s]]

instance (Show f, Show c) => Show (Symbol f c) where
  show (E s p) = show s ++ "^" ++ show p
  show (I i) = show i
  show (A a) = show a

instance (Ord f, Ord c) => ToSoP f c (Product f c) where
  toSoP p = simplifySoP $ S [p]

instance (Show f, Show c) => Show (Product f c) where
  show (P [s]) = show s
  show (P ss) = "(" ++ intercalate " * " (map show ss) ++ ")"

instance (Ord f, Ord c) => ToSoP f c (SoP f c) where
  toSoP = simplifySoP

instance (Show f, Show c) => Show (SoP f c) where
  show (S [p]) = show p
  show (S ps) = "(" ++ intercalate " + " (map show ps) ++ ")"

-- | Order relationship
data OrdRel
  = LeR -- ^ Less than or equal relationship
  | EqR -- ^ Equality relationship
  | GeR -- ^ Greater than or equal relationship
  deriving (Eq, Ord)

instance Show OrdRel where
  show LeR = "<="
  show EqR = "="
  show GeR = ">="

-- | Expression 
data SoPE f c
  = SoPE
    { lhs :: SoP f c -- ^ Left hand side of the expression
    , rhs :: SoP f c -- ^ Right hand side of the expression
    , op :: OrdRel -- ^ Relationship between sides
    }

instance (Eq f, Eq c) => Eq (SoPE f c) where
  (SoPE l1 r1 op1) == (SoPE l2 r2 op2)
    | op1 == op2
    , op1 == EqR
    -- a = b is the same as b = a
    = (l1 == l2) && (r1 == r2) || (l1 == r2) && (r1 == l2)
    | op1 == op2
    -- (a <= b) is itself
    = (l1 == l2) && (r1 == r2)
    | EqR `notElem` [op1,op2]
    -- (a <= b) is the same as (b >= a)
    = (l1 == r2) && (r1 == l2)
    | otherwise
    = False

instance (Show f, Show c) => Show (SoPE f c) where
  show SoPE{..} = unwords [show lhs, show op, show rhs]

-- | Creates an integer expression
int :: Integer -> SoP f c
int i = S [P [I i]]

-- | Creates expression from an atom
symbol :: Atom f c -> SoP f c
symbol a = S [P [A a]]

-- | Creates a constant expression
cons :: c -> SoP f c
cons c = S [P [A (C c)]]

-- | Creates a function expression
func :: (Ord f, Ord c) => f -> [SoP f c] -> SoP f c
func f args = S [P [A (F f (map simplifySoP args))]]


infixr 8 |^|
-- | Exponentiation of @SoP@s
(|^|) :: (Ord f, Ord c) => SoP f c -> SoP f c -> SoP f c
-- It's a B2 combinator,
(|^|) = (. simplifySoP) . normaliseExp

infixl 6 |+|
-- | Addition of @SoP@s
(|+|) :: (Ord f, Ord c) => SoP f c -> SoP f c -> SoP f c
(|+|) = mergeSoPAdd

infixl 7 |*|
-- | Multiplication of @SoP@s
(|*|) :: (Ord f, Ord c) => SoP f c -> SoP f c -> SoP f c
(|*|) = mergeSoPMul

infixl 6 |-|
-- | Subtraction of @SoP@s
(|-|) :: (Ord f, Ord c) => SoP f c -> SoP f c -> SoP f c
(|-|) = mergeSoPSub

infixl 7 |/|
-- | Division of @SoP@s
--
-- Produces a tuple of a quotient and a remainder
-- NB. Not implemented
(|/|) :: (Ord f, Ord c) => SoP f c -> SoP f c -> (SoP f c, SoP f c)
(|/|) = mergeSoPDiv

-- | Collects @Atom@s used in a @SoP@
atoms :: (Ord f, Ord c) => SoP f c -> Set (Atom f c)
atoms = S.unions . map atomsProduct . unS

-- | Collects @Atom@s used in a @Product@
--
-- Used by @atoms@
atomsProduct :: (Ord f, Ord c) => Product f c -> Set (Atom f c)
atomsProduct = S.unions . map atomsSymbol . unP

-- | Collect @Atom@s used in @Symbol@s
--
-- Used by @atomsProduct@
atomsSymbol :: (Ord f, Ord c) => Symbol f c
  -> Set (Atom f c) -- ^ - Empty - if the symbol is an integer
                    --   - Singleton - if the symbol is an atom
                    --   - Set of symbols - if the symbol is an exponentiation
atomsSymbol (I _) = S.empty
atomsSymbol (A a) = S.singleton a
atomsSymbol (E b p) = atoms b `union` atomsProduct p

-- | Collects constants used in @SoP@
--
-- Almost equivalent to
-- @Data.Set.filter isConst . atoms@
-- , but also collects constants used in functions
constants :: (Ord f, Ord c) => SoP f c -> Set c
constants = S.unions . map constsProduct . unS

-- | Collects constants used in @Product@
--
-- Used by @constants@
constsProduct :: (Ord f, Ord c) => Product f c -> Set c
constsProduct = S.unions . map constsSymbol . unP

-- | Collects constants used in @Symbol@
--
-- Used by @constsProduct@
constsSymbol :: (Ord f, Ord c) => Symbol f c -> Set c
constsSymbol (I _) = S.empty
constsSymbol (A a) = constsAtom a
constsSymbol (E b p) = constants b `union` constsProduct p

-- | Collects constants used in @Atom@
--
-- Used by @constsSymbol@
constsAtom :: (Ord f, Ord c) => Atom f c
  -> Set c -- ^ Singleton - if the atom is a constant
           --   Set of constants - if the atom is a function
constsAtom (C c) = S.singleton c
constsAtom (F _ args) = S.unions $ map constants args
