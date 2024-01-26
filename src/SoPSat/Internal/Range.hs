module SoPSat.Internal.Range
  ( Range(..)
  , Bound(..)
  , boundSoP
  , rangeAdd
  , rangeMul
  , rangeExp
  )
where

import SoPSat.SoP


data Bound f c
  = Bound (SoP f c)
  | Inf
  deriving (Eq, Show)

boundSoP :: Bound f c -> Maybe (SoP f c)
boundSoP (Bound s) = Just s
boundSoP Inf = Nothing

data Range f c
  = Range
    { lower :: Bound f c
    , upper :: Bound f c
    }
  deriving (Eq, Show)


boundAdd :: (Ord f, Ord c) => Bound f c -> Bound f c -> Bound f c
boundAdd Inf _   = Inf
boundAdd _   Inf = Inf
boundAdd (Bound a) (Bound b) = Bound (a |+| b)

boundMul :: (Ord f, Ord c) => Bound f c -> Bound f c -> Bound f c
boundMul Inf _   = Inf
boundMul _   Inf = Inf
boundMul (Bound a) (Bound b) = Bound (a |*| b)

boundExp :: (Ord f, Ord c) => Bound f c -> Bound f c -> Bound f c
boundExp Inf _   = Inf
boundExp _   Inf = Inf
boundExp (Bound a) (Bound b) = Bound (a |^| b)


rangeAdd :: (Ord f, Ord c) => Range f c -> Range f c -> Maybe (Range f c)
-- Subtraction of unbounded functions
rangeAdd (Range _   Inf) (Range Inf _  ) = Nothing
rangeAdd (Range Inf _  ) (Range _   Inf) = Nothing
rangeAdd (Range low1 up1) (Range low2 up2) = Just $
  Range (boundAdd low1 low2) (boundAdd up1 up2)

rangeMul :: (Ord f, Ord c) => Range f c -> Range f c -> Maybe (Range f c)
-- Multiplication of unbounded functions
rangeMul (Range Inf Inf) _               = Nothing
rangeMul _               (Range Inf Inf) = Nothing

-- Multiplication with infinitely increasing/decresing functions
rangeMul (Range low1 Inf) (Range low2 _) = Just $
  Range (boundMul low1 low2) Inf
rangeMul (Range low1 _) (Range low2 Inf) = Just $
  Range (boundMul low1 low2) Inf
rangeMul (Range Inf up1) (Range low2 _) = Just $
  Range Inf (boundMul up1 low2)
rangeMul (Range low1 _) (Range Inf up2) = Just $
  Range Inf (boundMul up2 low1)
rangeMul (Range low1 up1) (Range low2 up2) = Just $
  Range (boundMul low1 low2) (boundMul up1 up2)

-- rangeMul (Range low1 up1) (Range low2 up2)
-- --   | sopSign low1 == sopSign low2
-- --   = Range
-- rangeMul (Range low1 up1) (Range low2 up2) = let
--     low1Sign = sopSign =<< boundSoP low1
--     low2Sign = sopSign =<< boundSoP low2
--   in case (low1Sign,low2Sign) of
--        (Just Positive, Just Positive) -> Just $
--          Range (boundMul low1 low2) (boundMul up1 up2)
--        (Just Negative, Just Positive) -> Just $
--          Range (boundMul low1 up2) (boundMul up1 low2)
--        (Just Positive, Just Negative) -> Just $
--          Range (boundMul up1 low2) (boundMul low1 up2)
--        (Just Negative, Just Negative) -> Just $
--          Range (boundMul 
-- rangeMul _ _ = Nothing

rangeExp :: (Ord f, Ord c) => Range f c -> Range f c -> Maybe (Range f c)
rangeExp (Range Inf _) (Range Inf _) = Nothing
rangeExp (Range _ up1) (Range Inf up2) = Just $
  Range (Bound (int 0)) (boundExp up1 up2)
rangeExp (Range low1 up1) (Range low2 up2) = Just $
  Range (boundExp low1 low2) (boundExp up1 up2)

