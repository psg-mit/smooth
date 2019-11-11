{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving, DeriveFunctor #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}

module RevMode where

import Prelude
import Control.Arrow
import qualified Control.Category as C
import Control.Applicative (liftA2)
import Control.Monad (join)
import RealExpr (CMap (..), Additive (..))
import Data.Number.MPFR (MPFR)
import Data.MemoTrie
import qualified Rounded as R
import Interval (Interval, unitInterval)
import qualified Interval as I
import qualified Expr as E
import qualified RealExpr as RE
import qualified MPFR as M

-- http://conal.net/blog/posts/higher-dimensional-higher-order-derivatives-functionally

infixr :#
data Df g a b k = CMap (g, b) ((a, k) :->: Interval MPFR) :# Df g a b (a, k)
data a :~> b where
  D  :: CMap (a :->: Interval MPFR) b -> Df (a :->: Interval MPFR) a b () -> a :~> b

instance (HasTrie i, Additive v) => Additive (i :->: v) where
  zeroV = RE.tensor0 zeroV
  addV = RE.lift2mt addV

dZero :: HasTrie a => HasTrie k => Df g a b k
dZero = zeroV :# dZero

dShift :: Df g a b (c :->: k) -> Df g a (b, c) k
dShift (f :# f') = undefined

dSum :: HasTrie k => HasTrie a' =>
  Df a a' b k -> Df a a' b k -> Df a a' b k
dSum (f :# f') (g :# g') = fplusg :# dSum f' g' where
  fplusg = E.ap2 addV f g

unUnitTrie :: HasTrie i => ((i, ()) :->: a) -> i :->: a
unUnitTrie f = trie $ \i -> untrie f (i, ())

unitTrie :: HasTrie i => (i :->: a) -> (i, ()) :->: a
unitTrie f = trie $ \(i, ()) -> untrie f i

dId :: HasTrie i => i :~> (i :->: Interval MPFR)
dId = D C.id (arr (unitTrie . snd) :# dZero)

wknValue :: CMap g' g -> Df g a b k -> Df g' a b k
wknValue g (f :# f') = fg :# wknValue g f' where
  fg = proc (d', b) -> do
    d <- g -< d'
    f -< (d, b)

-- wknValueF :: (forall k. CMap (g, k) (Interval f) -> CMap (g', k) (Interval f)) -> Df f g a b k -> Df f g' a b k
-- wknValueF g (f :# f') = f2 :# wknValueF g f'
--   where
--   f1 = arr (\(g, (b, i)) -> (g, b, i)) >>> f
--   f1' = g f1
--   f2 = arr (\(g, b, i) -> (g, (b, i))) >>> f1'

tensorProd :: HasTrie i => HasTrie j =>
  CMap (a, b) c -> CMap g (i :->: a) -> CMap g (j :->: b)
  -> CMap g ((i, j) :->: c)
tensorProd f = E.ap2 (RE.tensor2 f)

selfTensor :: HasTrie i => CMap (a, a) a -> CMap g (i :->: a) -> CMap g ((i, i) :->: a)
selfTensor f x = tensorProd f x x

-- dSelfTensor :: Df g a b (a' :->: k) -> Df g a (b, b)

-- selfTensorDf :: Df g a c (a, a') -> Df g a c a'
-- selfTensorDf = undefined

linearD :: HasTrie u => CMap (u :->: Interval MPFR) (v :->: Interval MPFR) ->
  CMap (v :->: Interval MPFR) (u :->: Interval MPFR)
  -> u :~> (v :->: Interval MPFR)
linearD f ftr = D f $
  (arr unitTrie <<< ftr <<< arr snd) :# dZero

fstD :: HasTrie a => HasTrie b => Either a b :~> (a :->: Interval MPFR)
fstD = linearD (arr (\f -> trie (\i -> untrie f (Left i))))
  (arr (\f -> trie (\i -> case i of { Left i' -> untrie f i' ; Right _ -> I.lift R.zero })))

sndD :: HasTrie a => HasTrie b => Either a b :~> (b :->: Interval MPFR)
sndD = linearD (arr (\f -> trie (\i -> untrie f (Right i))))
  (arr (\f -> trie (\i -> case i of { Right i' -> untrie f i' ; Left _ -> I.lift R.zero })))

pairD' :: HasTrie k => HasTrie a =>
  Df d a b k -> Df d a c k -> Df d a (b, c) k
pairD' (f :# f') (g :# g') = fg :# (pairD' f' g') where
  fg = proc (d, (b, c)) -> do
    fi <- f -< (d, b)
    gi <- g -< (d, c)
    addV -< (fi, gi)

negate' :: HasTrie u => u :~> (u :->: Interval MPFR)
negate' = linearD neg neg where
  neg = RE.parallelmt (const RE.negate)

pairToEither :: HasTrie a => HasTrie b => (a :->: f, b :->: f) -> Either a b :->: f
pairToEither (l, r) = trie (either (untrie l) (untrie r))

eitherToPair :: HasTrie a => HasTrie b => (Either a b :->: f) -> (a :->: f, b :->: f)
eitherToPair f = let f' = untrie f in (trie (f' . Left) , trie (f' . Right))

transformOut :: CMap b' b -> Df g a b k -> Df g a b' k
transformOut b'b (f :# f') = f1 :# transformOut b'b f'
  where
  f1 = proc (g, b') -> do
    b <- b'b -< b'
    f -< (g, b)

pairD :: HasTrie g => HasTrie a => HasTrie b =>
  g :~> (a :->: f) -> g :~> (b :->: f) -> g :~> (Either a b :->: f)
pairD (D f f') (D g g') = D (f &&& g >>> arr pairToEither)
  (transformOut (arr eitherToPair) (pairD' f' g'))

(@.) :: HasTrie a => HasTrie b => b :~> c -> a :~> (b :->: Interval MPFR) -> a :~> c
(D g g') @. (D f f') = D (g <<< f) $
  let g1 = wknValue f g' in
    linCompose (transformK undefined g1) f'

dap1 :: HasTrie g => HasTrie a => a :~> b -> g :~> (a :->: Interval MPFR) -> g :~> b
dap1 f = (f @.)

dap2 :: HasTrie g => HasTrie a => HasTrie b =>
  Either a b :~> c ->
  g :~> (a :->: Interval MPFR) -> g :~> (b :->: Interval MPFR) -> g :~> c
dap2 f x y = f @. pairD x y

transformK :: HasTrie a =>
  CMap (g, (a, k) :->: Interval MPFR) ((a, k') :->: Interval MPFR)
  -> Df g a b k -> Df g a b k'
transformK kf (f :# f') = kff :# undefined -- transformK (RE.parallelmtg (const kf)) f'
  where
  kff = proc (g, b) -> do
    a <- f -< (g, b)
    kf -< (g, a)

dWkn :: Df g a (b :->: Interval MPFR) (a :->: ka)
     -> Df g a (b :->: Interval MPFR) (a :->: (a :->: ka))
dWkn = undefined

dWkn1 :: HasTrie b => CMap (g, k') k
     -> Df g b c (b, k')
     -> Df g b c (b, k)
dWkn1 e f = undefined --transformK (RE.parallelmtg (const e)) f

-- dWkn1' :: HasTrie b => CMap (g, (b :->: k')) (a :->: k')
--      -> Df g b c (b :->: (b :->: k'))
--      -> Df g b c (b :->: (a :->: k'))
-- dWkn1' e f = transformK (RE.parallelmtg (const e)) f

dWkn2 :: Df g a b k -> Df g' a' b' k'
dWkn2 = undefined


linCompose :: HasTrie a => HasTrie b => Additive ka =>
  Df g b c ka
  -> Df g a (b :->: Interval MPFR) ka -> Df g a c ka
linCompose f@(f0 :# f') g@(g0 :# g') = undefined -- g0f0 :# dSum gf' g'f
  where
  g0f0 = proc (g, c) -> do
    b <- f0 -< (g, c)
    g0 -< undefined -- (g, b)
  gf' = undefined -- linCompose (dWkn1 g0 f') (dWkn g)
  g'f = undefined -- linCompose (dWkn2 f') g'
-- linCompose g@(g0 :# g') f@(f0 :# f') =
--   (g0 <<< (arr fst &&& f2)) :# dSum (linCompose (dWkn1 f0' g') (dWkn (arr snd) f))
--                       (linCompose (dWkn (C.id *** arr snd) g) f')
--   where
--   f2 = proc (g, (a, ka)) -> do
--     b <- f0 -< (g, (a, ka))
--     returnA -< (b, ka)
--   f0' = proc (g, (b1, (a, ka))) -> do
--      b'ka' <- f2 -< (g, (a, ka))
--      returnA -< (b1, b'ka')


-- scalarMult :: VectorSpace v s => Df g g' s k -> Df g g' v k -> Df g g' v k
-- scalarMult s@(s0 :# s') x@(x0 :# x') =
--   E.ap2 (*^) s0 x0 :# dSum (scalarMult (dWkn (arr snd) s) x')
--                             (scalarMult s' (dWkn (arr snd) x))

-- dMult :: R.Rounded a => Df g g' (Interval a) k -> Df g g' (Interval a) k -> Df g g' (Interval a) k
-- dMult x@(x0 :# x') y@(y0 :# y') =
--   E.ap2 RE.mul x0 y0 :# dSum (dMult (dWkn (arr snd) x) y')
--                               (dMult x' (dWkn (arr snd) y))

-- dWkn1 :: CMap (g, k') k -> Df g a b k -> Df g a b k'
-- dWkn1 ext (f :# f') = (f <<< (arr fst &&& ext)) :# dWkn1 ext' f'
--   where
--   ext' = proc (g, (a, k')) -> do
--     k <- ext -< (g, k')
--     returnA -< (a, k)

-- dlinearWkn :: R.Rounded x => Additive b => Df g (a, Interval x) b k -> Df g a b k
-- dlinearWkn = dlinearWkn' id

-- dlinearWkn' :: R.Rounded x => Additive b => (forall d. CMap (d, k') b -> CMap (d, k) b) -> Df g (a, Interval x) b k' -> Df g a b k
-- dlinearWkn' z (f :# f') = z f :# dlinearWkn' z' f'
--   where
--   -- z' :: forall d. CMap (d, ((a, x), k')) b -> CMap (d, (a, k)) b
--   z' g = proc (d, (a, k)) -> do
--     g1 -< ((d, (a, I.lift R.zero)), k)
--     where
--     g' = proc ((d, ax), k') -> do
--       g -< (d, (ax, k'))
--     -- g1 :: CMap ((d, (a, x)), k) b
--     g1 = z g'

-- -- Seems right. Could inline scalarMult if I wanted
-- lift1 :: VectorSpace a a => CMap a a -> a :~> a -> a :~> a
-- lift1 f (D f') = D $ (f <<< arr fst) :# scalarMult (dWkn (arr snd) f') (arr (fst . snd) :# dZero)