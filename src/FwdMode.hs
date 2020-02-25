{-|
Forward-mode AD over `CMap`.
Admits higher-order derivatives, but not higher-order functions.
-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving, DeriveFunctor #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

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

dlinearWkn' :: forall a x b k k' g. R.Rounded x => Additive b =>
  (forall d. CMap (d, k') b -> CMap (d, k) b) -> Df g (a, Interval x) b k' -> Df g a b k
dlinearWkn' z (f :# f') = z f :# dlinearWkn' z' f'
  where
  z' :: forall d. CMap (d, ((a, Interval x), k')) b -> CMap (d, (a, k)) b
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

multD :: RE.CNum a => g :~> a -> g :~> a -> g :~> a
multD (D x) (D y) = D (dMult x y)

{-| Composition of two smooth maps yields a smooth map -}
(@.) :: Additive c => (b :~> c) -> (a :~> b) -> (a :~> c)
D g @. D f@(f0 :# _) = D (compose (wknValue (f0 <<< arr (\x -> (x, ()))) g) f)

data App g a b k = forall k'. App (Df g a b k') (CMap k k')

data CompPart' g a b c ka kb where
  Nil :: Df g b c () -> CompPart' g a b c ka ()
  Cons :: App g a b ka -> CompPart' g a b c ka kb -> CompPart' g a b c ka (b, kb)

data CompPart g a b c ka where
  CompPart :: CompPart' g a b c ka kb -> CompPart g a b c ka

wknApp :: App g a b k -> App g a b (a, k)
wknApp (App fk vars) = App fk (vars <<< arr snd)

wknCompPart' :: CompPart' g a b c ka kb -> CompPart' g a b c (a, ka) kb
wknCompPart' (Nil g) = Nil g
wknCompPart' (Cons x xs) = Cons (wknApp x) (wknCompPart' xs)

-- bloat :: a -> [[a]] -> [[[a]]]
-- bloat x  []      = [[[x]]]
-- bloat x (xs:xss) = ((x:xs):xss) : map (xs:) (bloat x xss)
bloat :: Df g a b (a, ()) -> CompPart g a b c k -> [CompPart g a b c (a, k)]
bloat f' (CompPart (Nil g)) = [CompPart (Cons (App f' (arr id *** arr (\_ -> ()))) (Nil g))]
bloat f' (CompPart (Cons xs@(App fk@(_ :# fk') vars) xss)) =
  let x1 = CompPart (Cons (App fk' (arr id *** vars)) (wknCompPart' xss)) in
  let x2 = (bloat f' (CompPart xss)) in
  x1 : map (\(CompPart c) -> CompPart (Cons (wknApp xs) c)) x2

getG :: CompPart' g a b c ka kb -> Df g b c kb
getG (Nil g) = g
getG (Cons x xs) = let _ :# g' = getG xs in g'

cplength :: CompPart' g a b c ka kb -> Int
cplength (Nil g) = 0
cplength (Cons x xs) = 1 + cplength xs

evalCompPart' :: CompPart' g a b c ka kb -> CMap (g, ka) kb
evalCompPart' (Nil _) = arr (\_ -> ())
evalCompPart' (Cons (App f x) part) = let fx :# _ = dWkn x f in fx &&& evalCompPart' part

evalCompPart'' :: CompPart' g a b c ka kb -> CMap (g, ka) c
evalCompPart'' x = let g :# _ = dWkn1 (evalCompPart' x) (getG x) in g

-- partitions :: [a] -> [[[a]]]
-- partitions  []    = [[]]
-- partitions (x:xs) = concatMap (bloat x) (partitions xs)
compose :: forall g a b c. Additive c => Df g b c () -> Df g a b () -> Df g a c ()
compose g f@(_ :# f') = go partitionsStart where
  go :: [CompPart g a b c ka] -> Df g a c ka
  go parts = foldr1 (E.ap2 addV) [ evalCompPart'' p | CompPart p <- parts ] :#
    go (concatMap (bloat f') parts)
  partitionsStart :: [CompPart g a b c ()]
  partitionsStart = [CompPart (Nil g)]

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

fromFuncs :: RE.CNum a => [CMap a a] -> a :~> a
fromFuncs = D . go 1
  where
  go :: RE.CNum a => CMap (a, k) a -> [CMap a a] -> Df a a a k
  go prods (f : fs) = ((f <<< arr fst) * prods) :# go ((prods <<< (arr id *** arr snd)) * arr (fst . snd)) fs

toFuncs :: RE.CNum a => a :~> a -> [CMap a a]
toFuncs (D f) = go f (arr (\_ -> ())) where
  go :: RE.CNum a => Df g a b k -> CMap g k -> [CMap g b]
  go (g :# g') y = (g <<< (C.id &&& y)) : go g' (1 &&& y)

-- Alternative version
-- lift1 :: RE.CNum a => CMap a a -> a :~> a -> a :~> a
-- lift1 f f' = fromFwd f (multD (f' @. fstD) sndD)

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
pow' 1 = dId
pow' k = lift1 (RE.pow k) (linearD ((fromIntegral k *) (arr id)) @. (pow' (k - 1)))

square'' :: R.Rounded a => Interval a :~> Interval a
square'' = lift1 (RE.pow 2) (linearD ((2 *) (arr id)))

partialIfThenElse :: R.Rounded a => CMap g (Maybe Bool) -> g :~> Interval a -> g :~> Interval a -> g :~> Interval a
partialIfThenElse cond (D (t :# t')) (D (f :# f')) = D ((RE.partialIfThenElse cond t1 f1 <<< arr (\(x, ()) -> x)) :# partialIfThenElse' cond t' f')
  where
  t1 = t <<< arr (\x -> (x, ()))
  f1 = f <<< arr (\x -> (x, ()))

getDerivTower :: RE.CNum a => a :~> a -> CMap g a -> [CMap g a]
getDerivTower (D f) x = go 1 (wknValue x f) (arr (\_ -> ())) where
  go :: RE.CNum a => CMap g a ->  Df g a b k -> CMap g k -> [CMap g b]
  go dx (g :# g') y = (g <<< (C.id &&& y)) : go 1 g' (dx &&& y)

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

-- The part of the fwd(f) that gives us these:
-- fwd(f)^(0)(x, v) = f^(1)(v)
-- fwd(f)^(1)(x, v)(dxa, dva) = f^(2)(v, dxa)
-- fwd(f)^(2)(x, v)(dxa, dva)(dxb, dvb) = f^(3)(v, dxa, dxb)
fwdDerU :: Df g g b (g, k) -> Df (g, g) (g, g) b k
fwdDerU = dWknA (arr fst) -- ignore all of the dv's
  . dWkn1' (arr (\((x, v), dxs) -> (x, (v, dxs)))) -- make the input v the first dx


fwdDerDU :: Additive b => CMap k' k ->
  Df g g b (g, k) -> Df (g, g) (g, g) b ((g, g), k')
fwdDerDU fext f@(f0 :# f') = f1 :#
  fwdDerDU fext' f'
  where
  f1 = proc ((x, u), ((dx, du), k')) -> do
    k <- fext -< k'
    f0 -< (x, (du, k))
  fext' = arr fst *** fext

fwdDerDUs :: Additive b => CMap k' k ->
  Df g g b (g, k) -> Df (g, g) (g, g) b ((g, g), k')
fwdDerDUs fext f'@(_ :# f'') =
  dSum (fwdDerDU fext f')
       (zeroV :# fwdDerDUs (arr fst *** fext) f'')

fwdDer' :: Additive b =>
  Df g g b k -> Df (g, g) (g, g) b k
fwdDer' (f :# f') = dSum (fwdDerU f') (zeroV :# fwdDerDUs (arr id) f')

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


-- A generalization of lift1. Give a continuous map for the value,
-- and a smooth map of the derivative for the rest.
fromFwd :: Additive a => CMap a b -> (a, a) :~> b -> a :~> b
fromFwd f (D f') = D $ (f <<< arr fst) :# convertFwdDeriv f'

-- the opposite of `fwdDerU`
convertFwdDeriv :: Additive g => Df (g, g) (g, g) b k -> Df g g b (g, k)
convertFwdDeriv = dWkn1' (arr (\(x, (v, dxs)) -> ((x, v), dxs)))
  . dWknA (arr id &&& zeroV) -- make all the dv's 0s