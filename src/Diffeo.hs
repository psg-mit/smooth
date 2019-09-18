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
data Df k a b = CMap k b :# Df (a, k) a b
deriving instance Functor (Df k a)
newtype a :~> b = D (Df a a b)

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

dZero :: Additive v => Df k g v
dZero = zeroV :# dZero

dConst :: Additive v => v :~> v
dConst = D $ C.id :# dZero

dSum :: Additive v => Df k g v -> Df k g v -> Df k g v
dSum (f :# f') (g :# g') = RE.ap2 (^+^) f g :# dSum f' g'

scalarMult :: VectorSpace v s => Df k g s -> Df k g v -> Df k g v
scalarMult s@(s0 :# s') x@(x0 :# x') =
  RE.ap2 (*^) s0 x0 :# dSum (scalarMult (dWkn (arr snd) s) x')
                            (scalarMult s' (dWkn (arr snd) x))

dMult :: R.Rounded a => Df k g (Interval a) -> Df k g (Interval a) -> Df k g (Interval a)
dMult x@(x0 :# x') y@(y0 :# y') =
  RE.ap2 RE.mul x0 y0 :# dSum (dMult (dWkn (arr snd) x) y')
                              (dMult x' (dWkn (arr snd) y))

dWkn :: CMap k' k -> Df k v g -> Df k' v g
dWkn ext (f :# f') = (f <<< ext) :# dWkn (C.id *** ext) f'

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
dId = D $ C.id :# arr fst :# dZero

linearD :: Additive v => CMap u v -> u :~> v
linearD f = D $ f :# (f <<< arr fst) :# dZero

fstD :: Additive a => (a,b) :~> a
fstD = linearD (arr fst)

sndD :: Additive b => (a,b) :~> b
sndD = linearD (arr snd)

pairD :: Df k g a -> Df k g b -> Df k g (a, b)
pairD (f :# f') (g :# g') = (f &&& g) :# (pairD f' g')

add :: R.Rounded a => (Interval a, Interval a) :~> Interval a
add = linearD RE.add


(@.) :: Additive c => (b :~> c) -> (a :~> b) -> (a :~> c)
(D g@(g0 :# g')) @. (D f@(f0 :# f')) = D $
  (g0 <<< f0) :# linCompose (dWkn (C.id *** f0) g') f'

linCompose :: Additive c => Df (b, ka) b c -> Df (a, ka) a b -> Df (a, ka) a c
linCompose g@(g0 :# g') f@(f0 :# f') =
  (g0 <<< f2) :# dSum (linCompose (dWkn (C.id *** f2) g') (dWkn (arr snd) f))
                      (linCompose (dWkn (C.id *** arr snd) g) f')
  where f2 = f0 &&& arr snd

dap1 :: Additive b => a :~> b -> g :~> a -> g :~> b
dap1 f = (f @.)

dap2 :: Additive c => (a, b) :~> c -> g :~> a -> g :~> b -> g :~> c
dap2 f (D x) (D y) = f @. D (pairD x y)

-- Seems right. Could inline scalarMult if I wanted
lift1 :: VectorSpace a a => CMap a a -> a :~> a -> a :~> a
lift1 f (D f') = D $ f :# scalarMult (dWkn (arr snd) f') (arr fst :# dZero)

negate' :: Interval MPFR :~> Interval MPFR
negate' = linearD RE.negate

exp' = lift1 M.exp' exp'

sin' = lift1 M.sin' cos'
cos' = lift1 M.cos' (negate' @. sin')

getDerivTower :: R.Rounded a => Interval a :~> Interval a -> CMap g (Interval a) -> [CMap g (Interval a)]
getDerivTower (D f) x = go f x where
  go :: R.Rounded a => Df k (Interval a) b -> CMap g k -> [CMap g b]
  go (g :# g') y = (g C.. y) : go g' (1 &&& y)

diffeoExample :: Int -> IO ()
diffeoExample n = E.runAndPrint $ E.asMPFR $ getDerivTower (exp' @. linearD ((*2) C.id)) (E.asMPFR 0) !! n