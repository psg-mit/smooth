{-|
Forward-mode AD over `CMap`.
Admits higher-order derivatives, but not higher-order functions.
-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving, DeriveFunctor #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module FwdMode where

import Prelude
import Control.Arrow
import qualified Control.Category as C
import Control.Applicative (liftA2)
import RealExpr (CMap (..), Additive (..), CPoint)
import qualified Rounded as R
import Interval (Interval, unitInterval)
import qualified Interval as I
import qualified Expr as E
import qualified RealExpr as RE
import qualified MPFR as M

-- http://conal.net/blog/posts/higher-dimensional-higher-order-derivatives-functionally

infixr :#

{-| `Df a a b ()` is a Taylor series for a smooth function `f : a -> b`.
  It is represented by a stream of continuous maps, for the function
  and all its derivatives:

  f  : (a, ()) -> b
  f' : (a, (a, ())) -> b
  f'' : (a, (a, (a, ()))) -> b
  ...

  Each of f, f', f'' is multilinear in all of the `a` arguments
  after the first one, which is the one around which the Taylor expansion
  is taken. We expect `a` and `b` to be vector spaces.

  `Df g a b ()` is "value pullback" of a Taylor series for a smooth
  function `f : a -> b`. For instance, if we apply `f` to a point
  `x : g -> a` (represented as a continuous map from some stage of
  definition `g`), then we get a Taylor series `Df g a b ()`.

  In general, we have `Df g a b k`, where the final argument `k`
  is useful for inductively characterizing the stream of derivatives.
  `k` essentially represents an unary natural number:
  () = 0
  (a, ()) = 1
  (a, (a, ())) = 2
  ...

  This allows us to inductively define the stream of derivatives.
  A `Df g a b k` is a stream of derivatives starting from the `k`th
  derivative.
-}
data Df g a b k = CMap (g, k) b :# Df g a b (a, k)

{-| `a :~> b` represents a smooth map from `a` to `b`,
    as a tower of continuous maps for its derivatives.
-}
newtype a :~> b = D (Df a a b ())


{-| Derivative towers form a vector space. Here we show
    that there is a zero `dZero`, and that you can add
    two derivative towers with `dSum`.
 -}
dZero :: Additive b => Df a a' b k
dZero = zeroV :# dZero

zeroD :: Additive b => a :~> b
zeroD = D dZero

bang :: g :~> ()
bang = D x where
  x :: Df g a () k
  x = RE.bang :# x

dSum :: Additive b => Df a a' b k -> Df a a' b k -> Df a a' b k
dSum (f :# f') (g :# g') = E.ap2 addV f g :# dSum f' g'

{-| A notion of vector spaces over some scalar type `s`,
    which we use to implement scalar multiplication as
    a smooth function.
-}
class Additive v => VectorSpace v where
  mulV    :: CMap (M.Real, v) v    -- scale a vector

instance VectorSpace () where
  mulV = arr (\(_, ()) -> ())

instance VectorSpace M.Real where
  mulV = RE.cmul

instance (VectorSpace v1, VectorSpace v2) => VectorSpace (v1, v2) where
  mulV = proc (s, (v1, v2)) -> do
    v1' <- mulV -< (s, v1)
    v2' <- mulV -< (s, v2)
    returnA -< (v1', v2')

scalarMult :: VectorSpace v => Df g g' M.Real k -> Df g g' v k -> Df g g' v k
scalarMult s@(s0 :# s') x@(x0 :# x') =
  E.ap2 mulV s0 x0 :# dSum (scalarMult (dWkn (arr snd) s) x')
                            (scalarMult s' (dWkn (arr snd) x))

dMult :: RE.CNum a => Df g g' a k -> Df g g' a k -> Df g g' a k
dMult x@(x0 :# x') y@(y0 :# y') =
  E.ap2 RE.cmul x0 y0 :# dSum (dMult (dWkn (arr snd) x) y')
                              (dMult x' (dWkn (arr snd) y))

wknValue :: CMap g' g -> Df g a b k -> Df g' a b k
wknValue g (f :# f') = (f <<< (g *** C.id)) :# wknValue g f'

wknValueF :: (forall k. CMap (g, k) b -> CMap (g', k) b) -> Df g a b k -> Df g' a b k
wknValueF g (f :# f') = g f :# wknValueF g f'

dWkn :: CMap k' k -> Df g a b k -> Df g a b k'
dWkn ext = dWkn1' (C.id *** ext)

dWkn1 :: CMap (g, k') k -> Df g a b k -> Df g a b k'
dWkn1 ext = dWkn1' (arr fst &&& ext)

dWkn1':: CMap (g', k') (g, k) -> Df g a b k -> Df g' a b k'
dWkn1' ext (f :# f') = (f <<< ext) :# dWkn1' ext' f'
  where
  ext' = proc (g', (a, k')) -> do
    (g, k) <- ext -< (g', k')
    returnA -< (g, (a, k))

restrictReal :: R.Rounded b => CMap g Bool -> Df g a (Interval b) k -> Df g a (Interval b) k
restrictReal mustHold (f :# f') = f1 :# restrictReal mustHold f'
  where
  f1 = proc (g, k) -> do
     b <- mustHold -< g
     y <- f -< (g, k)
     RE.restrictReal -< (b, y)

-- Combine partial results from two sources
join :: R.Rounded b => Df g a (Interval b) k -> Df g a (Interval b) k -> Df g a (Interval b) k
join (f :# f') (g :# g') = E.ap2 RE.join f g :# join f' g'

partialIfThenElse' :: R.Rounded b => CMap g (Maybe Bool) -> Df g a (Interval b) k -> Df g a (Interval b) k -> Df g a (Interval b) k
partialIfThenElse' cond t f = join (restrictReal (fmap (== Just True) cond) t)
                                   (restrictReal (fmap (== Just False) cond) f)

dWknA :: forall a' a g b k. CMap a' a -> Df g a b k -> Df g a' b k
dWknA fa = go (arr id) where
  go :: forall k' k. CMap k' k -> Df g a b k -> Df g a' b k'
  go fk (f :# f') = f1 :# go (fa *** fk) f' where
    f1 = proc (g, k') -> do
       k <- fk -< k'
       f -< (g, k)

dlinearWkn :: R.Rounded x => Additive b => Df g (a, Interval x) b k -> Df g a b k
dlinearWkn = dlinearWkn' id

dlinearWkn' :: R.Rounded x => Additive b => (forall d. CMap (d, k') b -> CMap (d, k) b) -> Df g (a, Interval x) b k' -> Df g a b k
dlinearWkn' z (f :# f') = z f :# dlinearWkn' z' f'
  where
  -- z' :: forall d. CMap (d, ((a, x), k')) b -> CMap (d, (a, k)) b
  z' g = proc (d, (a, k)) -> do
    g1 -< ((d, (a, I.lift R.zero)), k)
    where
    g' = proc ((d, ax), k') -> do
      g -< (d, (ax, k'))
    -- g1 :: CMap ((d, (a, x)), k) b
    g1 = z g'

{-| The identity function as a smooth map -}
dId :: Additive u => u :~> u
dId = D $ arr fst :# arr (fst . snd) :# dZero

{-| Given a continuous map `f : u -> v` that is linear,
    its smooth map representation is a derivative tower
    where f' = f and f'' = f''' = ... = 0.
-}
linearD :: Additive v => CMap u v -> u :~> v
linearD f = D $ (f <<< arr fst) :# (f <<< arr (fst . snd)) :# dZero

fstD :: Additive a => (a,b) :~> a
fstD = linearD (arr fst)

sndD :: Additive b => (a,b) :~> b
sndD = linearD (arr snd)

pairD' :: Df g g' a k -> Df g g' b k -> Df g g' (a, b) k
pairD' (f :# f') (g :# g') = (f &&& g) :# (pairD' f' g')

pairD :: g :~> a -> g :~> b -> g :~> (a, b)
pairD (D f) (D g) = D (pairD' f g)

add :: RE.CNum a => (a, a) :~> a
add = linearD RE.cadd

addD :: Additive a => g :~> a -> g :~> a -> g :~> a
addD (D x) (D y) = D (dSum x y)

scalarMultD :: VectorSpace v => g :~> M.Real -> g :~> v -> g :~> v
scalarMultD (D c) (D x) = D (scalarMult c x)

{-| Composition of two smooth maps yields a smooth map -}
(@.) :: Additive c => (b :~> c) -> (a :~> b) -> (a :~> c)
(D g@(g0 :# g')) @. (D f@(f0 :# f')) = D $
  (g0 <<< (f0 &&& arr snd)) :# linCompose (wknValue (f0 <<< (C.id &&& arr (\_ -> ()))) g') f'

{-| Composition of linear maps and their derivative towers yields
    a linear map with a derivative tower. Essentially, given two linear maps
    `g : b -> c` and `f : a -> b` with derivative towers, their composition
    is the derivative tower
    (g . f) = g . f
    (g . f)' = (g' . f) + (g . f')

    But there is some important "bookkeeping" and details beyond this.
-}
linCompose :: Additive c => Df g b c (b, ka) -> Df g a b (a, ka) -> Df g a c (a, ka)
linCompose g@(g0 :# g') f@(f0 :# f') =
  (g0 <<< (arr fst &&& f2)) :# dSum (linCompose (dWkn1 f0' g') (dWkn (arr snd) f))
                      (linCompose (dWkn (C.id *** arr snd) g) f')
  where
  f2 = proc (g, (a, ka)) -> do
    b <- f0 -< (g, (a, ka))
    returnA -< (b, ka)
  f0' = proc (g, (b1, (a, ka))) -> do
     b'ka' <- f2 -< (g, (a, ka))
     returnA -< (b1, b'ka')

{-| Apply a smooth function of 1 variable to a smooth argument. -}
dap1 :: Additive b => a :~> b -> g :~> a -> g :~> b
dap1 f = (f @.)

{-| Apply a smooth function of 2 variables to two smooth
    arguments at the same stage of definition. -}
dap2 :: Additive c => (a, b) :~> c -> g :~> a -> g :~> b -> g :~> c
dap2 f x y = f @. pairD x y

-- Seems right. Could inline scalarMult if I wanted
lift1 :: RE.CNum a => CMap a a -> a :~> a -> a :~> a
lift1 f (D f') = D $ (f <<< arr fst) :# dMult (dWkn (arr snd) f') (arr (fst . snd) :# dZero)

negate' :: RE.CNum a => a :~> a
negate' = linearD RE.cnegate

max' :: R.Rounded a => (Interval a, Interval a) :~> Interval a
max' = D $ (RE.max <<< arr fst) :# (RE.max_deriv <<< arr f)
  :# restrictReal RE.neq dZero
  where
  f (x, (dx, ())) = (x, dx)

min' :: R.Rounded a => (Interval a, Interval a) :~> Interval a
min' = D $ (RE.min <<< arr fst) :# (RE.min_deriv <<< arr f)
  :# restrictReal RE.neq dZero
  where
  f (x, (dx, ())) = (x, dx)

signum_deriv' :: R.Rounded a => Interval a :~> Interval a
signum_deriv' = lift1 RE.signum_deriv signum_deriv'

log', exp', sin', cos' :: RE.CFloating a => a :~> a
log' = lift1 RE.clog recip'
exp' = lift1 RE.cexp exp'
sin' = lift1 RE.csin cos'
cos' = lift1 RE.ccos (negate' @. sin')
recip' :: RE.CFractional a => a :~> a
recip' = lift1 RE.crecip (negate' @. recip' @. square')
square' :: RE.CNum a => a :~> a
square' = D $ (\(D x) -> dMult x x) dId
sqrt' :: RE.CFloating a => a :~> a
sqrt' = lift1 RE.csqrt (recip' @. linearD ((2 *) (arr id)) @. sqrt')
pow' :: R.Rounded a => Int -> Interval a :~> Interval a
pow' 0 = lift1 1 zeroD
pow' k = lift1 (RE.pow k) (linearD ((fromIntegral k *) (arr id)) @. (pow' (k - 1)))

partialIfThenElse :: R.Rounded a => CMap g (Maybe Bool) -> g :~> Interval a -> g :~> Interval a -> g :~> Interval a
partialIfThenElse cond (D (t :# t')) (D (f :# f')) = D ((RE.partialIfThenElse cond t1 f1 <<< arr (\(x, ()) -> x)) :# partialIfThenElse' cond t' f')
  where
  t1 = t <<< arr (\x -> (x, ()))
  f1 = f <<< arr (\x -> (x, ()))

getDerivTower :: R.Rounded a => Interval a :~> Interval a -> CMap g (Interval a) -> [CMap g (Interval a)]
getDerivTower (D f) x = go (wknValue x f) (arr (\_ -> ())) where
  go :: R.Rounded a => Df g (Interval a) b k -> CMap g k -> [CMap g b]
  go (g :# g') y = (g <<< (C.id &&& y)) : go g' (1 &&& y)

getValue :: g :~> a -> CMap g a
getValue (D (f :# f')) = f <<< arr (\x -> (x, ()))

fwdDeriv' :: Additive a => CMap ((g, (a, a)), k') ((g, a), k) -> Df (g, a) (g, a) b k -> Df (g, (a, a)) (g, (a, a)) b k'
fwdDeriv' g (f :# f') = (f <<< g) :# fwdDeriv' g2 f'
  where
  g2 = proc ((g', (x', dx')), ((g, (x, dx)), k')) -> do
    dx2 <- addV -< (x', dx)
    k <- g -< ((g, (x, dx2)), k')
    returnA -< ((g', dx'), k)

fwdDeriv :: Additive a => (g, a) :~> b -> (g, (a, a)):~> b
fwdDeriv (D f) = D (fwdDeriv' (arr (\((g, (a, da)), ()) -> ((g, a), ()))) f)

getDeriv :: Additive g => g :~> a -> g :~> a
getDeriv (D (f :# f')) = D (dWkn1 (zeroV &&& arr snd) f')

justDeriv :: Additive g => Additive a => g :~> a -> g :~> a
justDeriv (D f) = D (zeroV :# dWkn zeroV f)

genDeriv' :: Additive d => CMap (g, k) a
  -> Df g (d, a) b k -> Df g (d, a) b k
genDeriv' dx (f :# f') = dWkn1 ((zeroV &&& dx) &&& arr snd) f'

deriv' :: Additive d => R.Rounded a => Df g (d, Interval a) b k -> Df g (d, Interval a) b k
deriv' (f :# f') = dWkn ((zeroV &&& 1) &&& C.id) f'

deriv :: Additive g => R.Rounded a => (g, Interval a) :~> b -> (g, Interval a) :~> b
deriv (D f) = D (deriv' f)

-- The continuous map argument is the directional derivative
genDeriv :: Additive g => (g, a) :~> b -> CMap g a -> (g, a) :~> b
genDeriv (D f) dx = D $ genDeriv' (dx <<< arr (fst . fst)) f

genDeriv'' :: CMap (g, k) a
  -> Df g a b k -> Df g a b k
genDeriv'' dx (f :# f') = dWkn1 (dx &&& arr snd) f'

fwdDerDU :: Additive b => CMap k' k ->
  Df g g b (g, k) -> Df (g, g) (g, g) b ((g, g), k')
fwdDerDU fext f@(f0 :# f') = f1 :#
  fwdDerDU fext' f'
  where
  f1 = proc ((x, u), ((dx, du), k')) -> do
    k <- fext -< k'
    f0 -< (x, (du, k))
  fext' = arr fst *** fext

fwdDerU :: Df g g b (g, k) -> Df (g, g) (g, g) b k
fwdDerU = dWknA (arr fst) . dWkn1' (arr (\((x, dx), dxs) -> (x, (dx, dxs))))


fwdDerDUs :: Additive b => CMap k' k ->
  Df g g b (g, k) -> Df (g, g) (g, g) b ((g, g), k')
fwdDerDUs fext f'@(_ :# f'') =
  dSum (fwdDerDU fext f')
       (zeroV :# fwdDerDUs (arr fst *** fext) f'')

fwdDer' :: Additive b =>
  Df g g b k -> Df (g, g) (g, g) b k
fwdDer' (f :# f'@(f0' :# f'')) =
  dSum (fwdDerU f') (zeroV :# fwdDerDUs (arr id) f')

fwdDer :: Additive b => g :~> b -> (g, g) :~> b
fwdDer (D f) = D (fwdDer' f)

fwdWithValue :: Additive g => Additive b => g :~> b -> (g, g) :~> (b, b)
fwdWithValue f = pairD (f @. fstD) (fwdDer f)

fwdSecondDer :: Additive g => Additive b => g :~> b -> (g, (g, g)) :~> b
fwdSecondDer f = let f' = fwdDer f in
  fwdDer f' @. pairD (pairD fstD (fstD @. sndD)) (pairD (sndD @. sndD) zeroD)

{-| An example function. Calculates the `n`th derivative of
    (\x -> exp (2 * x)) at x = 0.
-}
diffeoExample :: Int -> CPoint M.Real
diffeoExample n = getDerivTower (exp' @. linearD ((*2) C.id)) (E.asMPFR 0) !! n



-- Below is experimental! It may be wrong! Be warned!


-- I am not sure this is correct at all!
-- A generalization of lift1. Give a continuous map for the value,
-- and a smooth map of the derivative for the rest.
fromFwd :: Additive a => CMap a b -> (a, a) :~> b -> a :~> b
fromFwd f (D f') = D $ (f <<< arr fst) :# convertFwdDeriv f'

convertFwdDeriv :: Additive a => Df (a, a) (a, a) b () -> Df a a b (a, ())
convertFwdDeriv = convertFwdDeriv' (arr id)

-- I am setting some derivatives to 0. Is that okay?
convertFwdDeriv' :: Additive a => CMap k' k -> Df (a, a) (a, a) b k -> Df a a b (a, k')
convertFwdDeriv' k'k (f :# f') = f1 :# convertFwdDeriv' k'knew f' where
  f1 = proc (x, (dx, k')) -> do
    k <- k'k -< k'
    f -< ((x, dx), k)
  k'knew = proc (a, k') -> do
    k <- k'k -< k'
    z <- zeroV -< ()
    returnA -< ((a, z), k)