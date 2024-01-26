{-# LANGUAGE RecordWildCards #-}

module SoPSat.Internal.SolverMonad
where

import Control.Monad.Trans.State.Strict
  ( StateT(..)
  , evalStateT
  , get
  , gets
  , put
  )

import Data.Map (Map)
import qualified Data.Map as M

import SoPSat.SoP
import qualified SoPSat.SoP as SoP
import SoPSat.Internal.SoP
  (Atom(..), Symbol(..), Product(..), SoP(..))
import SoPSat.Internal.Unify
import SoPSat.Internal.Range


data (Ord f, Ord c) => State f c
  = State (Map (Atom f c) (Range f c)) [Unifier f c]
  deriving (Show)

instance (Ord f, Ord c) => Semigroup (State f c) where
  (State r1 u1) <> (State r2 u2) = State (M.union r1 r2) (u1 ++ u2)

instance (Ord f, Ord c) => Monoid (State f c) where
  mempty = State M.empty []

-- TODO: Change Maybe to some MonadError for better error indication
type SolverState f c = StateT (State f c) Maybe


maybeFail :: (MonadFail m) => Maybe a -> m a
maybeFail (Just a) = return a
maybeFail Nothing = fail ""


getRanges :: (Ord f, Ord c) => SolverState f c (Map (Atom f c) (Range f c))
getRanges = gets (\(State rangeS _) -> rangeS)

getRange :: (Ord f, Ord c) => Atom f c -> SolverState f c (Range f c)
getRange c = maybeFail . M.lookup c =<< getRanges

getRangeSymbol :: (Ord f, Ord c) => Symbol f c -> SolverState f c (Range f c)
getRangeSymbol (E b p) = maybeFail =<< rangeExp <$> getRangeSoP b <*> getRangeProduct p
getRangeSymbol i@(I _) = return range
  where bound = Bound (toSoP i)
        range = Range bound bound
getRangeSymbol (A a)   = getRange a

getRangeProduct :: (Ord f, Ord c) => Product f c -> SolverState f c (Range f c)
getRangeProduct p = maybeFail . foldl rm oneRange =<< mapM getRangeSymbol (unP p)
  where
    one = Bound $ SoP.int 1
    oneRange = Just (Range one one)
    rm Nothing  _ = Nothing
    rm (Just a) b = rangeMul a b

getRangeSoP :: (Ord f, Ord c) => SoP f c -> SolverState f c (Range f c)
getRangeSoP s = maybeFail . foldl ra zeroRange =<< mapM getRangeProduct (unS s)
  where
    zero = Bound $ SoP.int 0
    zeroRange = Just (Range zero zero)
    ra Nothing _  = Nothing
    ra (Just a) b = rangeAdd a b

putRange :: (Ord f, Ord c) => Atom f c -> Range f c -> SolverState f c ()
putRange symb range@Range{..} = do
  -- Anti-symmetry: 5 <= x ^ x <= 5 => x = 5
  case (lower == upper, upper) of
    (True,Bound bound) -> putUnifiers [Subst symb (toSoP bound)]
    _                  -> return ()
  (State rangeS unifyS) <- get
  let rangeSn = M.insert symb range rangeS
  put (State rangeSn unifyS)


getUnifiers :: (Ord f, Ord c) => SolverState f c [Unifier f c]
getUnifiers = gets (\(State _ unifyS) -> unifyS)

putUnifiers :: (Ord f, Ord c) => [Unifier f c] -> SolverState f c ()
putUnifiers us = do
  (State rangeS unifyS) <- get
  put (State rangeS (substsSubst us unifyS ++ us))

-- | Puts a state to use during computations
withState :: (Ord f, Ord c) => State f c -> SolverState f c ()
withState = put

-- | Runs computation returning result and resulting state
runStatements :: (Ord f, Ord c) => SolverState f c a -> Maybe (a,State f c)
runStatements stmts = runStateT stmts mempty

-- | Similar to @runStatements@ but does not return final state
evalStatements :: (Ord f, Ord c) => SolverState f c a -> Maybe a
evalStatements stmts = evalStateT stmts mempty
