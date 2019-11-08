{-|
Lifting the module `Diffeo` into the category of
presheaves, adding higher-order functions. In particular,
we implement integration as a smooth higher-order function
of type `(R -> R) -> R`.
-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module FwdPSh where

import Prelude hiding (Real, max)
import Control.Arrow
import Control.Category (Category)
import qualified Control.Category as C
import RealExpr (CMap (..), Additive (..), Point)
import Data.Number.MPFR (MPFR)
import qualified Rounded as R
import Interval (Interval, unitInterval)
import qualified Expr as E
import qualified RealExpr as RE
import Experimental.PSh
import FwdMode
import qualified MPFR as M

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
  signum = dap1 (lift1 (signum C.id) signum_deriv')
  fromInteger x = D $ fromInteger x :# dZero
  negate = dap1 negate'

instance R.Rounded a => Fractional (R CMap (Interval a) g) where
  recip (R x) = R (recip x)
  fromRational = R Prelude.. fromRational

instance R.Rounded a => Fractional (g :~> Interval a) where
  recip = dap1 recip'
  fromRational x = D $ fromRational x :# dZero

max :: R.Rounded a => g :~> Interval a -> g :~> Interval a -> g :~> Interval a
max = dap2 max'

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

-- Maybe this is working!!!
integral' :: R.Rounded a => ((g, Interval a) :~> Interval a) -> (g :~> Interval a)
integral' (D f) = D $ dlinearWkn (wknValueF integ f)
  where
  integ :: R.Rounded a => CMap ((g, Interval a), k1) (Interval a) -> CMap (g, k1) (Interval a)
  integ h = RE.integral1' (h <<< arr (\((g, k), a) -> ((g, a), k)))

integral :: R.Rounded a => ((g, Interval a) :~> Interval a -> (g, Interval a) :~> Interval a)
  -> g :~> (Interval a)
integral f = integral' (f sndD)

asReal :: R CMap (Interval MPFR) g -> CMap g (Interval MPFR)
asReal (R x) = x

derivative :: Additive g => Additive b => R.Rounded a =>
  ((g, Interval a) :~> Interval a -> (g, Interval a) :~> b)
  -> g :~> Interval a -> g :~> b
derivative f x = deriv (f sndD) @. pairD dId x

fwd_deriv' :: Additive g => Additive a => Additive b =>
  (g, a) :~> b -> g :~> a -> g :~> a -> g :~> b
fwd_deriv' f x dx = dap2 (fwdDer f) (pairD dId x) (pairD zeroD dx)

fwd_deriv :: Additive g => Additive a => Additive b =>
  ((g, a) :~> a -> (g, a) :~> b) -> g :~> a -> g :~> a -> g :~> b
fwd_deriv f = fwd_deriv' (f sndD)

wkn :: Additive g => Additive a => g :~> a -> (g, x) :~> a
wkn f = f @. fstD

getDerivTower' :: R.Rounded a => (Interval a :~> Interval a -> Interval a :~> Interval a)
  -> CMap g (Interval a) -> [CMap g (Interval a)]
getDerivTower' f = getDerivTower (f dId)

example :: Int -> Point (Interval MPFR)
example n = getDerivTower' (\c -> integral (\x -> sin (wkn c * x))) 3 !! n

example2 :: Point (Interval MPFR)
example2 = getValue $ fwd_deriv (\c -> integral (\x -> abs (x - wkn c))) 0.6 1

-- I think this is right!
example3 :: Point (Interval MPFR) -> Int -> Point (Interval MPFR)
example3 y n = getDerivTower' (\z -> fwd_deriv (\x -> x^2) z z) y !! n


absExample :: Point (Interval MPFR) -> Int -> Point (Interval MPFR)
absExample y n = getDerivTower' (\c -> integral (\x -> abs (x - wkn c))) y !! n

internalDiffExample :: Point (Interval MPFR)
internalDiffExample = getValue $ derivative (\c -> integral (\x -> abs (x - wkn c))) 0.6

reluIntegralExample :: Point (Interval MPFR) -> Int -> Point (Interval MPFR)
reluIntegralExample y n =
  getDerivTower' (\c -> integral (\x -> max 0 (x - wkn c))) y !! n

reluExample :: Point (Interval MPFR) -> Int -> Point (Interval MPFR)
reluExample x n = getDerivTower' (max 0) x !! n