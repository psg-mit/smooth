{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, IncoherentInstances #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}

module DiffPSh where

import Prelude hiding (Real)
import Control.Arrow
import Control.Category (Category)
import qualified Control.Category as C
import Control.Applicative (liftA2)
import Control.Monad (join)
import RealExpr (CMap (..))
import Data.Number.MPFR (MPFR)
import qualified Rounded as R
import Interval (Interval, unitInterval)
import qualified Expr as E
import qualified RealExpr as E
import Experimental.Expr

-- http://conal.net/blog/posts/higher-dimensional-higher-order-derivatives-functionally

type a :-* b = a -> b
data D k a b g = D (b g) (Sm k a b g)
type Sm k a b = Arr k a (D k a b)

class PShD k f where
  pdmap :: Sm k a b g -> f b g -> f a g

-- `d` for Delta: smooth context
-- `g` for Gamma: continuous context
data RD k a d g = RD (Sm k d a g)
data ArrD k a b d g = ArrD (forall d'. Sm k d' d g -> a d' g -> b d' g)
data (a :** b) (d :: * -> *) (g :: *) = a d g :** b d g

instance Category k => PSh k (RD k a d) where
  pmap f (RD x) = RD (pmap f x)

instance PShD k (RD k a) where
  pdmap dg (RD f) = RD (f @. dg)

instance PShD k (ArrD k a b) where
  pdmap dg (ArrD f) = ArrD $ \e x -> f (dg @. e) x

-- instance PSh k (ArrD k a b d) where

instance (PShD k f, PShD k g) => PShD k (f :** g) where
  pdmap dg (f :** g) = pdmap dg f :** pdmap dg g

instance (Category k, PSh k a, PSh k b) => PSh k (D k a b) where
  pmap f (D x y) = D (pmap f x) (pmap f y)

class VectorSpace v s | v -> s where
  zeroV   :: v g                -- the zero vector
  (*^)    :: s g -> v g -> v g  -- scale a vector
  (^+^)   :: v g -> v g -> v g  -- add vectors
  negateV :: v g -> v g         -- additive inverse

class VectorSpace v s => InnerSpace v s | v -> s where
  (<.>) :: v g -> v g -> s g

constArr :: (forall g. b g) -> Arr k a b g
constArr x = Arr (\_ _ -> x)

dConst :: VectorSpace b s => b g -> D k a b g
dConst b = D b (DiffPSh.constArr dZero)

dZero :: VectorSpace b s => D k a b g
dZero = dConst zeroV

dId :: VectorSpace u s => Sm k u u g
dId = Arr (\d u -> D u (Arr (\d' du -> dConst du)))

linearD :: Category k => VectorSpace v s => Arr k u v g -> Sm k u v g
linearD (Arr f) = Arr (\d u -> D (f d u) (Arr (\d' du -> dConst (f (d C.. d') du))))

fstD :: Category k => VectorSpace a s => Sm k (a :* b) a g
fstD = linearD (Arr (\d (x :* y) -> x))

sndD :: Category k => VectorSpace b s => Sm k (a :* b) b g
sndD = linearD (Arr (\d (x :* y) -> y))

pairD :: Category k => Sm k g a d -> Sm k g b d -> Sm k g (a :* b) d
pairD (Arr f) (Arr g) = Arr $ \d x ->
  let D fx f'x = f d x
      D gx g'x = g d x
  in D (fx :* gx) (pairD f'x g'x)

(@.) :: Sm k b c g -> Sm k a b g -> Sm k a c g
Arr f @. Arr g = Arr $ \d a0 ->
  let D b0 b' = g d a0
      D c0 c' = f d b0
  in D c0 (c' @. b')

type Real = R CMap (Interval MPFR)

instance R.Rounded a => VectorSpace (R CMap (Interval a)) (R CMap (Interval a)) where
  zeroV = 0
  (*^) = (*)
  (^+^) = (+)
  negateV = negate

instance R.Rounded a => Num (R CMap (Interval a) g) where
  R x + R y = R (x + y)
  R x * R y = R (x * y)
  negate (R x) = R (negate x)
  R x - R y = R (x - y)
  abs (R x) = R (abs x)
  fromInteger = R . fromInteger
  signum (R x) = R (signum x)

lift2 :: (forall g. a g -> b g -> c g) -> Arr k d a g -> Arr k d b g -> Arr k d c g
lift2 op (Arr f) (Arr g) = Arr $ \d x -> op (f d x) (g d x)

lift1' :: (forall g. a g -> b g) -> Arr k d a g -> Arr k d b g
lift1' op (Arr f) = Arr $ \d x -> op (f d x)

instance (PSh k s, VectorSpace v s) => VectorSpace (Arr k a v) s where
  zeroV   = DiffPSh.constArr zeroV
  s *^ Arr f = Arr (\d x -> pmap d s *^ f d x)
  (^+^)   = lift2 (^+^)
  negateV = lift1' negateV

instance (PSh CMap a, R.Rounded b) => Num (D CMap a (R CMap (Interval b)) g) where
  fromInteger               = dConst . fromInteger
  D u0 u' + D v0 v'         = D (u0 + v0) (lift2 (+) u' v')
  D u0 u' - D v0 v'         = D (u0 - v0) (lift2 (-) u' v')
  u@(D u0 (Arr u')) * v@(D v0 (Arr v')) =
    D (u0 * v0) (Arr (\g da -> pmap g u * v' g da + u' g da * pmap g v))
  abs u@(D u0 (Arr u')) = D (abs u0) (Arr (\g da -> pmap g (signum u) * u' g da))
  -- not totally accurate for signum here, it should blow up at 0...
  signum (D u u') = D (signum u) (DiffPSh.constArr 0)

instance R.Rounded a => Fractional (R CMap (Interval a) g) where
  recip (R x) = R (recip x)
  fromRational = R . fromRational

instance (PSh CMap a, R.Rounded b) => Fractional (D CMap a (R CMap (Interval b)) g) where
  recip = lift1 recip (\u -> - recip (u^2))
  fromRational = dConst . fromRational

lift1 :: (PSh CMap a, R.Rounded b)
  => (forall g. R CMap (Interval b) g -> R CMap (Interval b) g)
  -> (forall g. D CMap a (R CMap (Interval b)) g -> D CMap a (R CMap (Interval b)) g)
  -> D CMap a (R CMap (Interval b)) g
  -> D CMap a (R CMap (Interval b)) g
lift1 f f' u@(D u0 (Arr u')) = D (f u0) (Arr (\g da -> u' g da * pmap g (f' u)))

instance VectorSpace u s => VectorSpace (D k a u) (D k a s) where
  zeroV = D zeroV $ DiffPSh.constArr zeroV
  D s (Arr s') *^ D x (Arr x') = D (s *^ x) (Arr (\g d -> s' g d *^ x' g d))
  D a (Arr a') ^+^ D b (Arr b') = D (a ^+^ b) (Arr (\g d -> a' g d ^+^ b' g d))
  negateV (D a (Arr a')) = D (negateV a) (Arr (\g d -> negateV (a' g d)))

-- Function application
(#) :: Category k => Arr k a b g -> a g -> b g
Arr f # x = f C.id x

square :: R.Rounded a => Sm CMap Real Real g
square = Arr $ \_ x -> (dId # x) ^ 2

cube :: R.Rounded a => Sm CMap Real Real g
cube = Arr $ \_ x -> (dId # x) ^ 3

unArr :: Arr k (R k a) (R k b) g -> forall d. k d g -> k d a -> k d b
unArr (Arr f) g x = y where
  R y = f g (R x)

getValue :: D k a b g -> b g
getValue (D x dx) = x

getDeriv :: D k a b g -> Sm k a b g
getDeriv (D x dx) = dx

getDerivTower :: D CMap Real b g -> [b g]
getDerivTower (D x (Arr dx)) = x : getDerivTower (dx C.id 1)

-- Crossing my fingers that this is right!
integrate_unit_interval :: Arr CMap Real Real g -> Real g
integrate_unit_interval f = R $
  E.secondOrderPrim (E.integral' 16 unitInterval) (unArr f (arr fst) (arr snd))

integral :: Sm CMap (Arr CMap Real Real) Real g
integral = linearD $ Arr $ \d x -> integrate_unit_interval x

asReal :: R CMap (Interval MPFR) g -> CMap g (Interval MPFR)
asReal (R x) = x

example2 :: IO ()
example2 = E.runAndPrint $ asReal $ getDerivTower ((\x -> abs (x ^ 2)) (dId # 2)) !! 1

constFunc :: Sm CMap Real (Arr CMap Real Real) g
constFunc = linearD $ Arr $ \_ c -> Arr (\d _ -> pmap d c)

-- constFunc1 :: RD CMap Real d g -> ArrD

type DReal = RD CMap Real

-- smoothToCont :: ArrD CMap DReal DReal d g
--             -> Arr CMap (d :* Real) Real g
-- smoothToCont (ArrD f) = Arr $ \_ x -> RD (f dId x)

-- integral' :: ArrD CMap DReal DReal d g
--           -> DReal d g
-- integral' f = RD $ (linearD $ Arr $ \d x -> integrate_unit_interval x)

-- example4 :: IO ()
-- example4 = E.runAndPrint $ asReal $
--   getDerivTower (func # 3) !! 1
--   where
--   func :: Sm CMap Real Real g
--   func = Arr $ \g c -> (integral # Arr (\d x -> pmap d c * x ^ 2))