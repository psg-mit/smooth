{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, IncoherentInstances #-}
{-# LANGUAGE StandaloneDeriving, DeriveFunctor #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE RankNTypes #-}

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
import qualified Expr as E
import qualified RealExpr as RE
import qualified MPFR as M

-- http://conal.net/blog/posts/higher-dimensional-higher-order-derivatives-functionally

infixr :#
data Df g a b k = CMap (g, k) b :# Df g a b (a, k)
newtype a :~> b = D (Df a a b ())

class Additive v where
  zeroV   :: CMap g v         -- the zero vector
  (^+^)   :: CMap (v, v) v    -- add vectors
  negateV :: CMap v v         -- additive inverse

class Additive v => VectorSpace v s | v -> s where
  (*^)    :: CMap (s, v) v    -- scale a vector

instance R.Rounded a => Additive (Interval a) where
  zeroV = 0
  (^+^) = RE.add
  negateV = RE.negate

instance R.Rounded a => VectorSpace (Interval a) (Interval a) where
  (*^) = RE.mul

dZero :: Additive b => Df a a' b k
dZero = zeroV :# dZero

dConst :: Additive v => v :~> v
dConst = D $ arr fst :# dZero

dSum :: Additive b => Df a a' b k -> Df a a' b k -> Df a a' b k
dSum (f :# f') (g :# g') = RE.ap2 (^+^) f g :# dSum f' g'

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

dWkn :: CMap k' k -> Df g a b k -> Df g a b k'
dWkn ext = dWkn1 (ext <<< arr snd)

dWkn1 :: CMap (g, k') k -> Df g a b k -> Df g a b k'
dWkn1 ext (f :# f') = (f <<< (arr fst &&& ext)) :# dWkn1 ext' f'
  where
  ext' = proc (g, (a, k')) -> do
    k <- ext -< (g, k')
    returnA -< (a, k)

-- dlinearWkn' :: (forall g. CMap (g, k) b -> CMap (g, k') b) -> Df (a, k) a b -> Df (a, k') a b
-- dlinearWkn' l (f :# f') = l f :# dlinearWkn' l f'

-- dlinearWkn1 :: (forall g. CMap (a, g) b -> CMap (a', g) b) -> Df k a b -> Df k a' b
-- dlinearWkn1 l (g :# g') = g :# go id id g' where
--   go swap z (f :# f') = z f :# go (inswap . swap) (swap l . z) f'
--   inswap l' f = l' (f <<< arr (\(a', (a, k)) -> (a, (a', k)))) <<< arr (\(a, (a', k)) -> (a', (a, k)))

-- dWknMap :: (forall g. CMap (g, x) b -> CMap g b) -> Df (k, x) (g, x) b -> Df k g b
-- dWknMap f (g :# g') = f g :# dWknMap undefined g' where
--   g'' = proc () -> do
--       g -< ((k, x), (g, x'))
  -- f2 = proc (g, (a, k)) -> do
  --    <- f -< ((g, a), k)

dId :: Additive u => u :~> u
dId = D $ arr fst :# arr (fst . snd) :# dZero

linearD :: Additive v => CMap u v -> u :~> v
linearD f = D $ (f <<< arr fst) :# (f <<< arr (fst . snd)) :# dZero

fstD :: Additive a => (a,b) :~> a
fstD = linearD (arr fst)

sndD :: Additive b => (a,b) :~> b
sndD = linearD (arr snd)

pairD :: Df g g' a k -> Df g g' b k -> Df g g' (a, b) k
pairD (f :# f') (g :# g') = (f &&& g) :# (pairD f' g')

add :: R.Rounded a => (Interval a, Interval a) :~> Interval a
add = linearD RE.add


(@.) :: Additive c => (b :~> c) -> (a :~> b) -> (a :~> c)
(D g@(g0 :# g')) @. (D f@(f0 :# f')) = D $
  (g0 <<< (f0 &&& arr snd)) :# linCompose (wknValue (f0 <<< (C.id &&& arr (\_ -> ()))) g') f'

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

dap1 :: Additive b => a :~> b -> g :~> a -> g :~> b
dap1 f = (f @.)

dap2 :: Additive c => (a, b) :~> c -> g :~> a -> g :~> b -> g :~> c
dap2 f (D x) (D y) = f @. D (pairD x y)

-- Seems right. Could inline scalarMult if I wanted
lift1 :: VectorSpace a a => CMap a a -> a :~> a -> a :~> a
lift1 f (D f') = D $ (f <<< arr fst) :# scalarMult (dWkn (arr snd) f') (arr (fst . snd) :# dZero)

negate' :: R.Rounded a => Interval a :~> Interval a
negate' = linearD RE.negate

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

diffeoExample :: Int -> IO ()
diffeoExample n = E.runAndPrint $ E.asMPFR $ getDerivTower (exp' @. linearD ((*2) C.id)) (E.asMPFR 0) !! n