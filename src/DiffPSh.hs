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

module DiffPSh where

import Prelude hiding (Real)
import Control.Arrow
import Control.Category (Category)
import qualified Control.Category as C
import RealExpr (CMap (..))
import Data.Number.MPFR (MPFR)
import qualified Rounded as R
import Interval (Interval, unitInterval)
import qualified Expr as E
import qualified RealExpr as RE
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
  signum = dap1 (lift1 (signum C.id) signum_deriv')
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

asMPFR :: g :~> Interval MPFR -> g :~> Interval MPFR
asMPFR x = x

wkn :: Additive g => Additive a => g :~> a -> (g, x) :~> a
wkn f = f @. fstD

example :: Int -> IO ()
example n = E.runAndPrint $ E.asMPFR $
  getDerivTower ((\c -> integral (\x -> sin (wkn c * x))) dId) 3 !! n



absExample :: (forall g. CMap g (Interval MPFR)) -> Int -> IO ()
absExample y n = E.runAndPrint $
  getDerivTower ((\c -> integral (\x -> abs (x - wkn c))) dId) y !! n

internalDiffExample :: IO ()
internalDiffExample = E.runAndPrint $ E.asMPFR $ getValue $
  derivative (\c -> integral (\x -> abs (x - wkn c))) 3