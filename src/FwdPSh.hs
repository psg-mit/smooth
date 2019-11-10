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
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

module FwdPSh where

import Prelude hiding (Real, max)
import Control.Arrow
import Control.Category (Category)
import qualified Control.Category as C
import RealExpr (CMap (..), Additive (..), Point)
import qualified Rounded as R
import Interval (Interval, unitInterval)
import qualified Expr as E
import qualified RealExpr as RE
import Experimental.PSh
import FwdMode
import qualified MPFR as M
import MPFR (Real)

type D = (:~>)

instance ConCat D where
  type Ok D a = Additive a
  id = dId
  (.) = (@.)

type CReal = R CMap Real
type DReal = R D Real

data ArrD a b (g :: *) = ArrD (forall d. Additive d => d :~> g -> a d -> b d)

instance RE.CNum a => Num (R CMap a g) where
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

instance R.Rounded a => Num (R D (Interval a) g) where
  R x + R y = R (x + y)
  R x * R y = R (x * y)
  negate (R x) = R (negate x)
  R x - R y = R (x - y)
  abs (R x) = R (abs x)
  fromInteger = R Prelude.. fromInteger
  signum (R x) = R (signum x)

instance R.Rounded a => Fractional (R CMap (Interval a) g) where
  recip (R x) = R (recip x)
  fromRational = R Prelude.. fromRational

instance R.Rounded a => Fractional (g :~> Interval a) where
  recip = dap1 recip'
  fromRational x = D $ fromRational x :# dZero

max :: R.Rounded a => g :~> Interval a -> g :~> Interval a -> g :~> Interval a
max = dap2 max'

instance Floating (g :~> Real) where
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
  sqrt = dap1 sqrt'

-- Maybe this is working!!!
integral' :: R.Rounded a => ((g, Interval a) :~> Interval a) -> (g :~> Interval a)
integral' (D f) = D $ dlinearWkn (wknValueF integ f)
  where
  integ :: R.Rounded a => CMap ((g, Interval a), k1) (Interval a) -> CMap (g, k1) (Interval a)
  integ h = RE.integral1' (h <<< arr (\((g, k), a) -> ((g, a), k)))

integral :: R.Rounded a => ((g, Interval a) :~> Interval a -> (g, Interval a) :~> Interval a)
  -> g :~> (Interval a)
integral f = integral' (f sndD)

asReal :: R CMap Real g -> CMap g Real
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

fwd_deriv1 :: Additive g => Additive a => Additive b =>
  (ArrD (R D a) (R D b) g) -> g :~> a -> g :~> a -> g :~> b
fwd_deriv1 (ArrD f) = fwd_deriv' (let R b = f fstD (R sndD) in b)

-- fwd_deriv1' :: Additive g => Additive a => Additive b =>

wkn :: Additive g => Additive a => g :~> a -> (g, x) :~> a
wkn f = f @. fstD

getDerivTower' :: R.Rounded a => (Interval a :~> Interval a -> Interval a :~> Interval a)
  -> CMap g (Interval a) -> [CMap g (Interval a)]
getDerivTower' f = getDerivTower (f dId)

example :: Int -> Point Real
example n = getDerivTower' (\c -> integral (\x -> sin (wkn c * x))) 3 !! n

example2 :: Point Real
example2 = getValue $ fwd_deriv (\c -> integral (\x -> abs (x - wkn c))) 0.6 1

-- I think this is right!
example3 :: Point Real -> Int -> Point Real
example3 y n = getDerivTower' (\z -> fwd_deriv (\x -> x^2) z z) y !! n


absExample :: Point Real -> Int -> Point Real
absExample y n = getDerivTower' (\c -> integral (\x -> abs (x - wkn c))) y !! n

internalDiffExample :: Point Real
internalDiffExample = getValue $ derivative (\c -> integral (\x -> abs (x - wkn c))) 0.6

reluIntegralExample :: Point Real -> Int -> Point Real
reluIntegralExample y n =
  getDerivTower' (\c -> integral (\x -> max 0 (x - wkn c))) y !! n

reluExample :: Point Real -> Int -> Point Real
reluExample x n = getDerivTower' (max 0) x !! n





-- Tangent spaces

data Tan f g where
   Tan :: Additive d => g :~> (d, d) -> f d -> Tan f g

class PShD f where
  dmap :: Additive d => Additive g => d :~> g -> f g -> f d

instance (PShD f) => PShD (Tan f) where
  dmap f (Tan gdd fd) = Tan (gdd @. f) fd

tangentValue :: Additive g => PShD f => Tan f g -> f g
tangentValue (Tan xdx f) = dmap (fstD @. xdx) f

tanRto :: (DReal :* DReal) g -> Tan DReal g
tanRto (R x :* R dx) = Tan (pairD x dx) (R dId)

tanRfrom :: Tan DReal g -> (DReal :* DReal) g
tanRfrom (Tan gdd (R fd)) = R (fstD @. x) :* R (sndD @. x) where
  x = fwdWithValue fd @. gdd

fwdGlobal :: (forall g. a g -> b g) -> Tan a g -> Tan b g
fwdGlobal f (Tan gdd fd) = Tan gdd (f fd)

scaleDerivRn :: VectorSpace v s => g :~> (v, v) -> g :~> s -> g :~> (v, v)
scaleDerivRn xdx c = pairD (fstD @. xdx) (scalarMultD c (sndD @. xdx))

exponentialMapRn :: VectorSpace v s => g :~> (v, v) -> g :~> s -> g :~> v
exponentialMapRn xdx c = addD (fstD @. xdx) (scalarMultD c (sndD @. xdx))

-- scaleDerivTan :: Tan f g -> g :~> Real -> Tan f g
-- scaleDerivTan (Tan xdx f) c = Tan (scaleDerivRn xdx c) f

fwd :: Additive g => PShD a => ArrD a b g -> ArrD (Tan a) (Tan b) g
fwd (ArrD f) = ArrD $ \ext (Tan xdx ax) -> let f1 = f fstD (dmap sndD ax) in
  Tan (pairD (pairD ext (fstD @. xdx)) (pairD zeroD (sndD @. xdx))) f1

tanProdfrom :: Tan (a :* b) g -> (Tan a :* Tan b) g
tanProdfrom (Tan xdx (a :* b)) = Tan xdx a :* Tan xdx b

tanProdto :: PShD a => PShD b => (Tan a :* Tan b) g -> Tan (a :* b) g
tanProdto (Tan xdx a :* Tan ydy b) = Tan (pairD xy dxdy) (a' :* b') where
  xy = pairD (fstD @. xdx) (fstD @. ydy)
  dxdy = pairD (sndD @. xdx) (sndD @. ydy)
  a' = dmap fstD a
  b' = dmap sndD b

tanToRto :: Additive g => ArrD a (DReal :* DReal) g -> Tan (ArrD a DReal) g
tanToRto (ArrD f) = Tan (pairD (pairD dId 0) (pairD zeroD 1))
  (ArrD $ \ext a -> let g :* dg = f (fstD @. ext) a in
    g + (R (sndD @. ext)) * dg)

-- Haven't thought about this one too carefully,
-- so I should make sure it's correct
tanToRfrom :: Additive g => PShD a => Tan (ArrD a DReal) g -> (ArrD a (DReal :* DReal)) g
tanToRfrom (Tan xdx (ArrD f)) = ArrD $ \ext a ->
  let R z = f fstD (dmap sndD a) in
  let x = fwdWithValue z @. (pairD (pairD (fstD @. xdx @. ext) dId) (pairD (sndD @. xdx @. ext) zeroD)) in
  R (fstD @. x) :* R (sndD @. x)

-- a test of using `fromFwd`. Appears to be working properly!
testSqrt :: Real :~> Real
testSqrt = fromFwd RE.csqrt $
  recip (2 * (testSqrt @. fstD)) * sndD