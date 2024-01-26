{-# LANGUAGE RecordWildCards #-}

module SoPSat.Internal.Unify
where

import Data.List (intersect, (\\), nub, partition, find)
import Data.Function (on)

import SoPSat.SoP
  (toSoP, (|+|), (|-|), (|*|), (|^|))
import qualified SoPSat.SoP as SoP
import SoPSat.Internal.SoP
  (Atom(..), Symbol(..), Product(..), SoP(..))


data Unifier f c
  = Subst { sConst :: Atom f c
          , sSoP   :: SoP f c
          }
  deriving (Eq, Show)

substsSoP :: (Ord f, Ord c) => [Unifier f c] -> SoP f c -> SoP f c
substsSoP [] u = u
substsSoP ((Subst{..}):s) u = substsSoP s (substSoP sConst sSoP u)

substSoP :: (Ord f, Ord c) => Atom f c -> SoP f c -> SoP f c -> SoP f c
substSoP cons subs = foldr1 (|+|) . map (substProduct cons subs) . unS

substProduct :: (Ord f, Ord c) => Atom f c -> SoP f c -> Product f c -> SoP f c
substProduct cons subs = foldr1 (|*|) . map (substSymbol cons subs) . unP

substSymbol :: (Ord f, Ord c) => Atom f c -> SoP f c -> Symbol f c -> SoP f c
substSymbol _ _ s@(I _) = toSoP s
substSymbol cons subst s@(A a)
  | cons == a = subst
  | otherwise = S [P [s]]

substSymbol cons subst (E b p) = substSoP cons subst b |^| substProduct cons subst p

substsSubst :: (Ord f, Ord c) => [Unifier f c] -> [Unifier f c] -> [Unifier f c]
substsSubst s = map subst
  where
    subst sub@(Subst {..}) = sub { sSoP = substsSoP s sSoP }

unifiers :: (Ord f, Ord c) => SoP f c -> SoP f c -> [Unifier f c]
unifiers (S [P [A a]]) (S []) = [Subst a (S [P [I 0]])]
unifiers (S []) (S [P [A a]]) = [Subst a (S [P [I 0]])]

unifiers (S [P [I _]]) (S [P [I _]]) = []

-- (z ^ a) ~ (z ^ b) ==> [a := b]
unifiers (S [P [E s1 p1]]) (S [P [E s2 p2]])
  | s1 == s2 = unifiers (toSoP p1) (toSoP p2)

-- (2*e ^ d) ~ (2*e*a*c) ==> [a*c := 2*e ^ (d-1)]
unifiers (S [P [E (S [P s1]) p1]]) (S [P p2])
  | all (`elem` p2) s1
  = let base = s1 `intersect` p2
        diff = p2 \\ s1
    in unifiers (S [P diff]) (S [P [E (S [P base]) (P [I (-1)]),E (S [P base]) p1]])

unifiers (S [P p2]) (S [P [E (S [P s1]) p1]])
  | all (`elem` p2) s1
  = let base = s1 `intersect` p2
        diff = p2 \\ s1
    in unifiers (S [P diff]) (S [P [E (S [P base]) (P [I (-1)]),E (S [P base]) p1]])

-- (i ^ a) ~ j ==> [a := round (logBase i j)], when `i` and `j` are integers,
unifiers (S [P [E (S [P [I i]]) p]]) (S [P [I j]])
  = case integerLogBase i j of
      Just k  -> unifiers (S [p]) (S [P [I k]])
      Nothing -> []

unifiers  (S [P [I j]]) (S [P [E (S [P [I i]]) p]])
  = case integerLogBase i j of
      Just k  -> unifiers (S [p]) (S [P [I k]])
      Nothing -> []

-- x ^ i = j => [x := root i j]
unifiers (S [P [E s (P [I p])]]) (S [P [I j]])
  = case integerRt p j of
      Just k -> unifiers s (S [P [I k]])
      Nothing -> []

unifiers (S [P [I j]]) (S [P [E s (P [I p])]])
  = case integerRt p j of
      Just k -> unifiers s (S [P [I k]])
      Nothing -> []

-- a^d * a^e ~ a^c ==> [c := d + e]
unifiers (S [P [E s1 p1]]) (S [p2]) = case collectBases p2 of
  Just (b:bs,ps) | all (== s1) (b:bs) ->
    unifiers (S [p1]) (S ps)
  _ -> []

unifiers (S [p2]) (S [P [E s1 p1]]) = case collectBases p2 of
  Just (b:bs,ps) | all (== s1) (b:bs) ->
    unifiers (S ps) (S [p1])
  _ -> []

-- (i * a) ~ (j * b) ==> [a := (div j i) * b]
-- Where 'a' and 'b' are variables, 'i' and 'j' are integer literals, and j `mod` i == 0
unifiers (S [P ((I i):ps)]) (S [P ((I j):ps1)])
  | (Just k) <- safeDiv j i = unifiers (S [P ps]) (SoP.int k |*| S [P ps1])
  | (Just k) <- safeDiv i j = unifiers (SoP.int k |*| S [P ps]) (S [P ps1])
  | otherwise = []

-- (2*a) ~ (2*b) ==> [a := b]
-- unifiers (S [P (p:ps1)]) (S [P (p':ps2)])
--     | p == p'   = unifiers' ct (S [P ps1]) (S [P ps2])
--     | otherwise = []
unifiers (S [P ps1@(_:_:_)]) (S [P ps2])
    | null psx  = []
    | otherwise = unifiers (S [P ps1'']) (S [P ps2''])
  where
    ps1'  = ps1 \\ psx
    ps2'  = ps2 \\ psx
    ps1'' | null ps1' = [I 1]
          | otherwise = ps1'
    ps2'' | null ps2' = [I 1]
          | otherwise = ps2'
    psx  = ps1 `intersect` ps2

unifiers (S [P ps1]) (S [P ps2@(_:_:_)])
    | null psx  = []
    | otherwise = unifiers (S [P ps1'']) (S [P ps2''])
  where
    ps1'  = ps1 \\ psx
    ps2'  = ps2 \\ psx
    ps1'' | null ps1' = [I 1]
          | otherwise = ps1'
    ps2'' | null ps2' = [I 1]
          | otherwise = ps2'
    psx  = ps1 `intersect` ps2

unifiers (S [P [A a]]) s = [Subst a s]
unifiers s (S [P [A a]]) = [Subst a s]

-- (2 + a) ~ 5 ==> [a := 3]
unifiers (S ((P [I i]):ps1)) (S ((P [I j]):ps2))
    | i < j     = unifiers (S ps1) (S (P [I (j-i)]:ps2))
    | i > j     = unifiers (S (P [I (i-j)]:ps1)) (S ps2)

-- (a + c) ~ (b + c) ==> [a := b]
unifiers s1@(S ps1) s2@(S ps2) = case splitSoP s1 s2 of
  (s1',s2')
    | s1' /= s1 || s2' /= s2
    -> unifiers s1' s2'
  _ | null psx
    , length ps1 == length ps2
    -> case nub (concat (zipWith (\x y -> unifiers (S [x]) (S [y])) ps1 ps2)) of
        []  -> unifiers' s1 s2
        [k] -> [k]
        _   -> []
    | null psx
    -> unifiers' s1 s2
  _ -> unifiers' (S ps1'') (S ps2'')
  where
    ps1'  = ps1 \\ psx
    ps2'  = ps2 \\ psx
    ps1'' | null ps1' = [P [I 0]]
          | otherwise = ps1'
    ps2'' | null ps2' = [P [I 0]]
          | otherwise = ps2'
    psx = ps1 `intersect` ps2

unifiers' :: (Ord f, Ord c) => SoP f c -> SoP f c -> [Unifier f c]
unifiers' (S [P [I i],P [A a]]) s2
  = [Subst a (s2 |+| S [P [I (negate i)]])]
unifiers' s1 (S [P [I i],P [A a]])
  = [Subst a (s1 |+| S [P [I (negate i)]])]
unifiers' _ _ = []


splitSoP :: (Ord f, Ord c) => SoP f c -> SoP f c -> (SoP f c, SoP f c)
splitSoP u v = (lhs, rhs)
  where
    reduced = v |-| u
    (lhs',rhs') = partition neg (unS reduced)
    lhs | null lhs' = SoP.int 0
        | otherwise = ((|*|) `on` S) lhs' [P [I (-1)]]
    rhs | null rhs' = SoP.int 0
        | otherwise = S rhs'

    neg (P ((I i):_)) = i < 0
    neg _ = False
    
collectBases :: Product f c -> Maybe ([SoP f c],[Product f c])
collectBases = fmap unzip . traverse go . unP
  where
    go (E s1 p1) = Just (s1,p1)
    go _         = Nothing

safeDiv :: Integer -> Integer -> Maybe Integer
safeDiv i j
  | j == 0    = Just 0
  | otherwise = case divMod i j of
                  (k,0) -> Just k
                  _     -> Nothing

integerLogBase :: Integer -> Integer -> Maybe Integer
integerLogBase x y | x > 1 && y > 0 =
  let z1 = integerLogBase' x y
      z2 = integerLogBase' x (y-1)
  in  if z1 == z2
         then Nothing
         else Just z1
integerLogBase _ _ = Nothing

integerLogBase' :: Integer -> Integer -> Integer
integerLogBase' b m = snd (go b)
  where
    go :: Integer -> (Integer, Integer)
    go pw | m < pw = (m, 0)
    go pw = case go (pw ^ 2) of
              (q, e) | q < pw -> (q, 2 * e)
              (q, e) -> (q `quot` pw, 2 * e + 1)

-- Naive implementation of exact integer root
integerRt :: Integer -> Integer -> Maybe Integer
integerRt 1 y = Just y
integerRt x y = find ((== y) . (^ x)) [1..y]

