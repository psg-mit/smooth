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
type a :~> b = Df a a b

class VectorSpace v s | v -> s where
  zeroV   :: CMap g v          -- the zero vector
  (*^)    :: CMap (s, v) v    -- scale a vector
  (^+^)   :: CMap (v, v) v    -- add vectors
  negateV :: CMap v v         -- additive inverse

instance R.Rounded a => VectorSpace (Interval a) (Interval a) where
  zeroV = 0
  (*^) = RE.mul
  (^+^) = RE.add
  negateV = RE.negate

dZero :: VectorSpace v s => Df k g v
dZero = zeroV :# dZero

dConst :: VectorSpace v s => v :~> v
dConst = C.id :# dZero

dSum :: VectorSpace v s => Df k g v -> Df k g v -> Df k g v
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

dId :: VectorSpace u s => u :~> u
dId = C.id :# arr fst :# dZero

linearD :: VectorSpace v s => CMap u v -> u :~> v
linearD f = f :# (f <<< arr fst) :# dZero

fstD :: VectorSpace a s => (a,b) :~> a
fstD = linearD (arr fst)

sndD :: VectorSpace b s => (a,b) :~> b
sndD = linearD (arr snd)

pairD :: Df k g a -> Df k g b -> Df k g (a, b)
pairD (f :# f') (g :# g') = (f &&& g) :# (pairD f' g')

add :: R.Rounded a => (Interval a, Interval a) :~> Interval a
add = linearD RE.add



-- I think this is wrong somehow
composeIH :: VectorSpace b s' => VectorSpace c s => CMap ka kb -> Df (a, ka) a b -> Df (b, kb) b c -> Df (a, ka) a c
composeIH f f1@(f' :# f'') g1@(g' :# g'') =
  (g' <<< f_all) :# dSum (composeIH f_all f'' (dWkn (arr snd) g1))
                         (composeIH f_all (dWkn (arr snd) f1) g'')
  where
  -- and it's likely this part
  f_all = proc (a, ka) -> do
    kb <- f -< ka
    b <- f' -< (a, ka)
    returnA -< (b, kb)


(@.) :: VectorSpace b s' => VectorSpace c s => (b :~> c) -> (a :~> b) -> (a :~> c)
g@(g0 :# g') @. f@(f0 :# f') = (g0 <<< f0) :# linCompose (dWkn (C.id *** f0) g') f'
  -- (g0 <<< f0) :# linCompose (dWkn f0 g') f'
  -- (g0 <<< f0) :# composeIH f0 f' g'

linCompose :: VectorSpace c s => Df (b, ka) b c -> Df (a, ka) a b -> Df (a, ka) a c
linCompose g@(g0 :# g') f@(f0 :# f') =
  (g0 <<< f2) :# dSum (linCompose (dWkn (C.id *** f2) g') (dWkn (arr snd) f))
                      (linCompose (dWkn (C.id *** arr snd) g) f')
  where f2 = f0 &&& arr snd

dap1 :: VectorSpace a s' => VectorSpace b s => a :~> b -> g :~> a -> g :~> b
dap1 f = (f @.)

dap2 :: VectorSpace (a, b) s' => VectorSpace c s => (a, b) :~> c -> g :~> a -> g :~> b -> g :~> c
dap2 f x y = f @. pairD x y

-- Seems right. Could inline scalarMult if I wanted
lift1 :: VectorSpace a a => CMap a a -> a :~> a -> a :~> a
lift1 f f' = f :# scalarMult (dWkn (arr snd) f') (arr fst :# dZero)

lift1' :: VectorSpace u s => CMap u u -> (Df k a u -> Df (a, k) a s)
       -> Df k a u -> Df k a u
lift1' f f' u@(u0 :# u') = (f <<< u0) :# scalarMult (f' u) u'

lift1'' :: VectorSpace a a => CMap a a -> a :~> a -> a :~> a
lift1'' f f' = lift1' f (\x -> dWkn (arr snd) (f' @. x)) dId

negate' = linearD RE.negate

exp' = lift1 M.exp' exp'

sin' = lift1 M.sin' cos'
cos' = lift1 M.cos' (negate' @. sin')

getDerivTower :: R.Rounded a => Interval a :~> Interval a -> CMap g (Interval a) -> [CMap g (Interval a)]
getDerivTower f x = go f x where
  go :: R.Rounded a => Df k (Interval a) b -> CMap g k -> [CMap g b]
  go (g :# g') y = (g C.. y) : go g' (1 &&& y)

diffeoExample :: Int -> IO ()
diffeoExample n = E.runAndPrint $ E.asMPFR $ getDerivTower (exp' @. linearD ((*2) C.id)) (E.asMPFR 0) !! n