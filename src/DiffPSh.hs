{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, IncoherentInstances #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

module DiffPSh where

import Prelude hiding (Real)
import Control.Arrow
import Control.Category (Category)
import qualified Control.Category as C
import Control.Applicative (liftA2)
import Control.Monad (join)
import RealExpr (CMap (..))
import Data.Number.MPFR (MPFR)
import qualified Rounded as R
import Interval (Interval, unitInterval)
import qualified Expr as E
import qualified RealExpr as E
import Experimental.PSh
import Diffeo

type D = (:~>)

instance ConCat D where
  type Ok D a = Additive a
  id = dId
  (.) = (@.)

type Real = R CMap (Interval MPFR)
type DReal = R D (Interval MPFR)

instance R.Rounded a => Num (R CMap (Interval a) g) where
  R x + R y = R (x + y)
  R x * R y = R (x * y)
  negate (R x) = R (negate x)
  R x - R y = R (x - y)
  abs (R x) = R (abs x)
  fromInteger = R Prelude.. fromInteger
  signum (R x) = R (signum x)

instance R.Rounded a => Num (g :~> Interval a) where
  (+) = dap2 add
  D x * D y = D (dMult x y)
  abs = dap1 (lift1 (abs C.id) (signum dId))
  -- not totally accurate for signum here, it should blow up at 0...
  signum = dap1 (lift1 (signum C.id) 0)
  fromInteger x = D $ fromInteger x :# dZero
  negate = dap1 negate'

instance R.Rounded a => Fractional (R CMap (Interval a) g) where
  recip (R x) = R (recip x)
  fromRational = R Prelude.. fromRational

instance R.Rounded a => Fractional (g :~> Interval a) where
  recip = dap1 recip'
  fromRational x = D $ fromRational x :# dZero

instance Floating (g :~> Interval MPFR) where
  pi = D $ pi :# dZero
  log = dap1 log'
  exp = dap1 exp'
  sin = dap1 sin'
  cos = dap1 cos'
  -- tan      = lift1 tan $ recip . join (*) . cos
  -- asin     = lift1 asin $ \x -> recip (sqrt (1 - join (*) x))
  -- acos     = lift1 acos $ \x -> negate (recip (sqrt (1 - join (*) x)))
  -- atan     = lift1 atan $ \x -> recip (1 + join (*) x)
  -- sinh     = lift1 sinh cosh
  -- cosh     = lift1 cosh sinh
  -- tanh     = lift1 tanh $ recip . join (*) . cosh
  -- asinh    = lift1 asinh $ \x -> recip (sqrt (1 + join (*) x))
  -- acosh    = lift1 acosh $ \x -> recip (sqrt (join (*) x - 1))
  -- atanh    = lift1 atanh $ \x -> recip (1 - join (*) x)

-- Crossing my fingers that this is right!
integrate_unit_interval :: Arr CMap Real Real g -> Real g
integrate_unit_interval f = R $
  E.secondOrderPrim (E.integral' 16 unitInterval) (unArr f (arr fst) (arr snd))

integral1' :: R.Rounded a => CMap (g, Interval a) (Interval a) -> CMap g (Interval a)
integral1' = E.secondOrderPrim (E.integral' 16 unitInterval)

-- integral1 :: R.Rounded a => ((g, Interval a) :~> Interval a) -> (g :~> Interval a)
-- integral1 (D f) = D $ (dWkn integral1' f)

--
integral :: (Arr D DReal DReal) g -> DReal g
integral (Arr f) = undefined -- linearD $ Arr $ \d x -> integrate_unit_interval x

asReal :: R CMap (Interval MPFR) g -> CMap g (Interval MPFR)
asReal (R x) = x

-- example4 :: IO ()
-- example4 = E.runAndPrint $ asReal $
--   getDerivTower (func # 3) !! 1
--   where
--   func :: Sm CMap Real Real g
--   func = Arr $ \g c -> (integral # Arr (\d x -> pmap d c * x ^ 2))