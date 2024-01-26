module SoPSat.Internal.SoP
where

-- External
import Data.Either (partitionEithers)
import Data.List (sort)

-- | Atomic part of a @SoP@
-- like constants and unknown functions
data Atom f c
  = C c -- ^ Constant
  | F f [SoP f c] -- ^ Unknown function
  deriving (Eq, Ord)

-- | The most basic part used during reasoning:
-- - Numbers
-- - Atoms
-- - Exponents
data Symbol f c
  = I Integer -- ^ Number in an expression
  | A (Atom f c) -- ^ Atom in an expression
  | E (SoP f c) (Product f c) -- ^ Exponentiation
  deriving (Eq, Ord)

-- | Product of symbols
newtype Product f c = P { unP :: [Symbol f c] }
  deriving Eq

instance (Ord f, Ord c) => Ord (Product f c) where
  compare (P [x])   (P [y])   = compare x y
  compare (P [_])   (P (_:_)) = LT
  compare (P (_:_)) (P [_])   = GT
  compare (P xs)    (P ys)    = compare xs ys

-- | Sum of Products
newtype SoP f c = S { unS :: [Product f c] }
  deriving Ord

instance (Eq f, Eq c) => Eq (SoP f c) where
  (S []) == (S [P [I 0]]) = True
  (S [P [I 0]]) == (S []) = True
  (S ps1) == (S ps2)      = ps1 == ps2


mergeWith :: (a -> a -> Either a a) -> [a] -> [a]
mergeWith _ [] = []
mergeWith op (f:fs) = case partitionEithers $ map (`op` f) fs of
                        ([],_) -> f : mergeWith op fs
                        (updated,untouched) -> mergeWith op (updated ++ untouched)

reduceExp :: (Ord f, Ord c) => Symbol f c -> Symbol f c
reduceExp (E _             (P [I 0])) = I 1
reduceExp (E (S [P [I 0]]) _        ) = I 0
reduceExp (E (S [P [I i]]) (P [I j]))
  | j >= 0 = I (i ^ j)

reduceExp (E (S [P [E k i]]) j) =
  case normaliseExp k (S [e]) of
    (S [P [s]]) -> s
    _           -> E k e
  where e = P . sort . map reduceExp $ mergeWith mergeS (unP i ++ unP j)

reduceExp s = s

mergeS :: (Ord f, Ord c) => Symbol f c -> Symbol f c
       -> Either (Symbol f c) (Symbol f c)
mergeS (I i) (I j) = Left (I (i * j))
mergeS (I 1) r     = Left r
mergeS l     (I 1) = Left l
mergeS (I 0) _     = Left (I 0)
mergeS _     (I 0) = Left (I 0)

-- x * x^4 ==> x^5
mergeS s (E (S [P [s']]) (P [I i]))
  | s == s'
  = Left (E (S [P [s']]) (P [I (i + 1)]))

-- x^4 * x ==> x^5
mergeS (E (S [P [s']]) (P [I i])) s
  | s == s'
  = Left (E (S [P [s']]) (P [I (i + 1)]))

-- 4^x * 2^x ==> 8^x
mergeS (E (S [P [I i]]) p) (E (S [P [I j]]) p')
  | p == p'
  = Left (E (S [P [I (i*j)]]) p)

-- y*y ==> y^2
mergeS l r
  | l == r
  = case normaliseExp (S [P [l]]) (S [P [I 2]]) of
      (S [P [e]]) -> Left  e
      _           -> Right l

-- x^y * x^(-y) ==> 1
mergeS (E s1 (P p1)) (E s2 (P (I i:p2)))
  | i == (-1)
  , s1 == s2
  , p1 == p2
  = Left (I 1)

-- x^(-y) * x^y ==> 1
mergeS (E s1 (P (I i:p1))) (E s2 (P p2))
  | i == (-1)
  , s1 == s2
  , p1 == p2
  = Left (I 1)

mergeS l _ = Right l

mergeP :: (Eq f, Eq c) => Product f c -> Product f c
       -> Either (Product f c) (Product f c)
-- 2xy + 3xy ==> 5xy
mergeP (P ((I i):is)) (P ((I j):js))
  | is == js = Left . P $ I (i + j) : is
-- 2xy + xy  ==> 3xy
mergeP (P ((I i):is)) (P js)
  | is == js = Left . P $ I (i + 1) : is
-- xy + 2xy  ==> 3xy
mergeP (P is) (P ((I j):js))
  | is == js = Left . P $ I (j + 1) : is
-- xy + xy ==> 2xy
mergeP (P is) (P js)
  | is == js  = Left . P $ I 2 : is
  | otherwise = Right $ P is

normaliseExp :: (Ord f, Ord c) => SoP f c -> SoP f c -> SoP f c
-- b^1 ==> b
normaliseExp b (S [P [I 1]]) = b

-- x^(2xy) ==> x^(2xy)
normaliseExp b@(S [P [A _]]) (S [e]) = S [P [E b e]]

-- 2^(y^2) ==> 4^y
normaliseExp b@(S [P [_]]) (S [e@(P [_])]) = S [P [reduceExp (E b e)]]

-- (x + 2)^2 ==> x^2 + 4xy + 4
normaliseExp b (S [P [I i]]) | i > 0 =
  foldr1 mergeSoPMul (replicate (fromInteger i) b)

-- (x + 2)^(2x) ==> (x^2 + 4xy + 4)^x
normaliseExp b (S [P (e@(I i):es)]) | i >= 0 =
  -- Without the "| i >= 0" guard, normaliseExp can loop with itself
  -- for exponentials such as: 2^(n-k)
  normaliseExp (normaliseExp b (S [P [e]])) (S [P es])

-- (x + 2)^(xy) ==> (x+2)^(xy)
normaliseExp b (S [e]) = S [P [reduceExp (E b e)]]

-- (x + 2)^(y + 2) ==> 4x(2 + x)^y + 4(2 + x)^y + (2 + x)^yx^2
normaliseExp b (S e) = foldr1 mergeSoPMul (map (normaliseExp b . S . (:[])) e)

zeroP :: Product f c -> Bool
zeroP (P ((I 0):_)) = True
zeroP _ = False

mkNonEmpty :: (Ord f, Ord c) => SoP f c -> SoP f c
mkNonEmpty (S []) = S [P [I 0]]
mkNonEmpty s      = s

simplifySoP :: (Ord f, Ord c) => SoP f c -> SoP f c
simplifySoP = repeatF go
  where
    go = mkNonEmpty
       . S
       . sort . filter (not . zeroP)
       . mergeWith mergeP
       . map (P . sort . map reduceExp . mergeWith mergeS . unP)
       . unS

    repeatF f x =
      let x' = f x
      in  if x' == x
             then x
             else repeatF f x'
{-# INLINEABLE simplifySoP #-}

mergeSoPAdd :: (Ord f, Ord c) => SoP f c -> SoP f c -> SoP f c
mergeSoPAdd (S ps1) (S ps2) = simplifySoP $ S (ps1 ++ ps2)

mergeSoPMul :: (Ord f, Ord c) => SoP f c -> SoP f c -> SoP f c
mergeSoPMul (S ps1) (S ps2) = simplifySoP . S
  $ concatMap (zipWith (\p1 p2 -> P (unP p1 ++ unP p2)) ps1 . repeat) ps2

mergeSoPSub :: (Ord f, Ord c) => SoP f c -> SoP f c -> SoP f c
mergeSoPSub a b = mergeSoPAdd a (mergeSoPMul (S [P [I (-1)]]) b)

mergeSoPDiv :: (Ord f, Ord c) => SoP f c -> SoP f c -> (SoP f c, SoP f c)
mergeSoPDiv (S _ps1) (S _ps2) = undefined
