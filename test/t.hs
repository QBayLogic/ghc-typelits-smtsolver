{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE CPP                       #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoImplicitPrelude         #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE RoleAnnotations           #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE StandaloneDeriving        #-}

#if __GLASGOW_HASKELL__ >= 805
{-# LANGUAGE NoStarIsType              #-}
#endif

{-# OPTIONS_GHC -fplugin GHC.TypeLits.SoPSat #-}
{-# OPTIONS_GHC -dcore-lint #-}

import GHC.TypeLits
#if MIN_VERSION_base(4,18,0)
  hiding (type SNat)
#endif

import Unsafe.Coerce
import Prelude hiding (head,tail,init,(++),splitAt,concat,drop)
import qualified Prelude as P

import Data.Kind (Type)
import Data.List (isInfixOf)
import Data.Proxy
import Data.Type.Equality
import Control.Exception
import Test.Tasty
import Test.Tasty.HUnit

-- data Fin (n :: Nat) where
--   FZ :: Fin (n + 1)
--   FS :: Fin n -> Fin (n + 1)

-- test16 :: forall n . Integer -> Fin n
-- test16 n = case n of
--   0 -> FZ
--   x -> FS (test16 @(n-1) (x-1))

main = putStrLn "Hello World"

-- lemma2
--   :: forall j n
--   .  ( j <= n, 1 <= (n-j) )
--   => ( (j+1) <=? n ) :~: 'True
-- lemma2 = Refl

urk :: False :~: True
urk = case sub @0 of Refl -> ineq @(0 - 1)
  where
    ineq :: forall k. (1 <=? 1 + k) :~: True
    ineq = Refl

    sub :: forall n m. (m ~ (n - 1)) => 1 + (n - 1) :~: n
    sub = Refl -- bogus
