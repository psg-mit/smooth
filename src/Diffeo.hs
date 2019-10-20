{-|
Forward-mode AD over `CMap`.
Admits higher-order derivatives, but not higher-order functions.
-}

{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving, DeriveFunctor #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Diffeo where

import Prelude
import Control.Arrow
import qualified Control.Category as C
import Control.Applicative (liftA2)
import Control.Monad (join)
import RealExpr (CMap (..))
import Data.Number.MPFR (MPFR)
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

{-| A typeclass for the structure of vector spaces
    needed for computing derivatives.
-}
class Additive v where
  zeroV  :: CMap g v         -- the zero vector
  addV   :: CMap (v, v) v    -- add vectors

instance Additive () where
  zeroV = arr (\_ -> ())
  addV = arr (\_ -> ())

instance (Additive u, Additive v) => Additive (u, v) where
  zeroV = zeroV &&& zeroV
  addV = proc ((u1, v1), (u2, v2)) -> do
    u <- addV -< (u1, u2)
    v <- addV -< (v1, v2)
    returnA -< (u, v)

instance R.Rounded a => Additive (Interval a) where
  zeroV = 0
  addV = RE.add

{-| Derivative towers form a vector space. Here we show
    that there is a zero `dZero`, and that you can add
    two derivative towers with `dSum`.
 -}
dZero :: Additive b => Df a a' b k
dZero = zeroV :# dZero

zeroD :: Additive b => a :~> b
zeroD = D dZero

dSum :: Additive b => Df a a' b k -> Df a a' b k -> Df a a' b k
dSum (f :# f') (g :# g') = RE.ap2 addV f g :# dSum f' g'

{-| A notion of vector spaces over some scalar type `s`,
    which we use to implement scalar multiplication as
    a smooth function.
-}
class Additive v => VectorSpace v s | v -> s where
  (*^)    :: CMap (s, v) v    -- scale a vector

instance R.Rounded a => VectorSpace (Interval a) (Interval a) where
  (*^) = RE.mul

scalarMult :: VectorSpace v s => Df g g' s k -> Df g g' v k -> Df g g' v k
scalarMult s@(s0 :# s') x@(x0 :# x') =
  RE.ap2 (*^) s0 x0 :# dSum (scalarMult (dWkn (arr snd) s) x')
                            (scalarMult s' (dWkn (arr snd) x))

dMult :: R.Rounded a => Df g g' (Interval a) k -> Df g g' (Interval a) k -> Df g g' (Interval a) k
dMult x@(x0 :# x') y@(y0 :# y') =
  RE.ap2 RE.mul x0 y0 :# dSum (dMult (dWkn (arr snd) x) y')
                              (dMult x' (dWkn (arr snd) y))

wknValue :: CMap g' g -> Df g a b k -> Df g' a b k
wknValue g (f :# f') = (f <<< (g *** C.id)) :# wknValue g f'

wknValueF :: (forall k. CMap (g, k) b -> CMap (g', k) b) -> Df g a b k -> Df g' a b k
wknValueF g (f :# f') = g f :# wknValueF g f'

dWkn :: CMap k' k -> Df g a b k -> Df g a b k'
dWkn ext = dWkn1 (ext <<< arr snd)

dWkn1 :: CMap (g, k') k -> Df g a b k -> Df g a b k'
dWkn1 ext (f :# f') = (f <<< (arr fst &&& ext)) :# dWkn1 ext' f'
  where
  ext' = proc (g, (a, k')) -> do
    k <- ext -< (g, k')
    returnA -< (a, k)

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

add :: R.Rounded a => (Interval a, Interval a) :~> Interval a
add = linearD RE.add

addD :: Additive a => g :~> a -> g :~> a -> g :~> a
addD (D x) (D y) = D (dSum x y)

{-| Composition of two smooth maps yields a smooth map -}
(@.) :: Additive c => (b :~> c) -> (a :~> b) -> (a :~> c)
(D g@(g0 :# g')) @. (D f@(f0 :# f')) = D $
  (g0 <<< (f0 &&& arr snd)) :# linCompose (wknValue (f0 <<< (C.id &&& arr (\_ -> ()))) g') f'

{-| Composition of linear maps and their derivative towers yields
    a linear map with a derivative tower. Essentially, given two linear maps
    `g : b -> c` and `f : a -> b` with derivative towers, their composition
    is the derivative tower
    (g . f) = g . f
    (g . f)' = (g' . f) + (g + f')

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
lift1 :: VectorSpace a a => CMap a a -> a :~> a -> a :~> a
lift1 f (D f') = D $ (f <<< arr fst) :# scalarMult (dWkn (arr snd) f') (arr (fst . snd) :# dZero)

negate' :: R.Rounded a => Interval a :~> Interval a
negate' = linearD RE.negate

signum_deriv' :: R.Rounded a => Interval a :~> Interval a
signum_deriv' = lift1 RE.signum_deriv signum_deriv'
log' = lift1 M.log' recip'
exp' = lift1 M.exp' exp'
sin' = lift1 M.sin' cos'
cos' = lift1 M.cos' (negate' @. sin')
recip' :: R.Rounded a => Interval a :~> Interval a
recip' = lift1 RE.recip (negate' @. recip' @. square')
square' :: R.Rounded a => Interval a :~> Interval a
square' = D $ (\(D x) -> dMult x x) dId

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

fwdDerU :: Additive b =>
  Df g g b (g, k) -> Df (g, g) (g, g) b k
fwdDerU (f' :# f'') = f1 :# dWkn (arr fst *** arr id) (fwdDerU f'')
  where
  f1 = proc ((x, u), k) -> do
    f' -< (x, (u, k))

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

{-| An example function. Calculates the `n`th derivative of
    (\x -> exp (2 * x)) at x = 0.
-}
diffeoExample :: Int -> IO ()
diffeoExample n = E.runAndPrint $ E.asMPFR $ getDerivTower (exp' @. linearD ((*2) C.id)) (E.asMPFR 0) !! n