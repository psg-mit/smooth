{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving, RankNTypes #-}
{-# LANGUAGE TypeOperators, TypeFamilies, FlexibleContexts #-}
module SelfContained.Differentiable where

import Control.Category
import Control.Monad (MonadPlus)
import Control.Arrow
import Prelude hiding (id, (.))

import Unsafe.Coerce (unsafeCoerce)

class Cartesian k => NumCat k a where
  addC :: (a, a) `k` a
  mulC :: (a, a) `k` a
  negateC :: a `k` a
  negateC = subC . prod (fromIntegerC 0) id
  subC :: (a, a) `k` a
  -- subC = addC . prod proj1 (negateC . proj2)
  absC :: a `k` a
  signumC :: a `k` a
  fromIntegerC :: Integer -> g `k` a

instance (Cartesian k, NumCat k a) => Num (g `k` a) where
  (+) = lift2 addC
  (*) = lift2 mulC
  abs = lift1 absC
  (-) = lift2 subC
  negate = lift1 negateC
  signum = lift1 signumC
  fromInteger = fromIntegerC

class Additive k where
  zeroC :: () `k` a
  plusC :: (a, a) `k` a

instance MonadPlus m => Additive (Kleisli m) where
  zeroC = zeroArrow
  plusC = arr fst <+> arr snd

class Category k => Cartesian k where
  dup :: a `k` (a, a)
  proj1 :: (a, b) `k` a
  proj2 :: (a, b) `k` b
  prod :: g `k` a -> g `k` b -> g `k` (a, b)
  unit :: g `k` ()

class Category k => Extends k g g' where
  project :: g' `k` g
  lift :: g `k` a -> g' `k` a
  lift = (. project)

instance Category k => Extends k a a where
  project = id

instance Cartesian k => Extends k g (g, a) where
  project = proj1

type PSh k a g = g `k` a

lift1 :: Category k => (a `k` b) -> g `k` a -> g `k` b
lift1 f x = f . x

lift2 :: Cartesian k => ((a, b) `k` c) -> g `k` a -> g `k` b -> g `k` c
lift2 f x y = f . prod x y

unlift1 :: Cartesian k => (forall g. g `k` a -> g `k` b) -> a `k` b
unlift1 f = f id

unlift2 :: Cartesian k => (forall g. g `k` a -> g `k` b -> g `k` c) -> (a, b) `k` c
unlift2 f = f proj1 proj2

matchPair :: Cartesian k => g `k` (a, b) -> (forall d. Extends k g d => d `k` a -> d `k` b -> d `k` c) -> g `k` c
matchPair p f = f (proj1 . p) (proj2 . p)

quantifier :: Cartesian k => (forall g'.  (g', a) `k` b -> g' `k` b) -> forall g. (forall d. Extends k g d => d `k` a -> d `k` b) -> g `k` b
quantifier quant f = quant (f proj2)

type Del a = a



newtype FDiff k a b = FDiff (k (a, Del a) (b, Del b))
-- Would be great if I could make this into a single map
--  a `k` (b, Del b --> Del a)
-- if only I had an internal hom

data RDiff k a b = RDiff (k a b) (k (a, Del b) (b, Del a))

instance Category k => Category (FDiff k) where
  id = FDiff id
  FDiff g . FDiff f = FDiff (g . f)

instance Cartesian k => Cartesian (FDiff k) where
  dup = FDiff (prod (dup . proj1) (dup . proj2))
  proj1 = FDiff (prod (proj1 . proj1) (proj1 . proj2))
  proj2 = FDiff (prod (proj2 . proj1) (proj2 . proj2))
  prod (FDiff f) (FDiff g) = FDiff (prod (prod (proj1 . f) (proj1 . g)) (prod (proj2 . f) (proj2 . g)))
  unit = FDiff (prod unit unit)

instance Cartesian k => Category (RDiff k) where
  id = RDiff id id
  RDiff g gd . RDiff f fd = RDiff (g . f)
    (prod (proj1 . proj2) (proj2 . fd . prod proj1 (proj2 . proj2)) . prod proj1 (gd . prod (f . proj1) proj2))

instance (Additive k, Cartesian k) => Cartesian (RDiff k) where
  dup = RDiff dup (prod (dup . proj1) (plusC . proj2))
  proj1 = RDiff proj1 (prod (proj1 . proj1) (prod id (zeroC . unit) . proj2))
  proj2 = RDiff proj2 (prod (proj2 . proj1) (prod (zeroC . unit) id . proj2))
  prod (RDiff f fd) (RDiff g gd) = RDiff (prod f g)
    (prod (prod (proj1 . proj1) (proj1 . proj2)) (lift2 plusC (proj2 . proj1) (proj2 . proj2)) .
     prod (lift2 fd proj1 (proj1 . proj2)) (lift2 gd proj1 (proj2 . proj2))
    )
  unit = RDiff unit (prod unit (zeroC . unit))

instance NumCat k a => NumCat (FDiff k) a where
  addC = FDiff (prod (addC . proj1) (addC . proj2))
  mulC = FDiff (prod (mulC . proj1) (lift2 addC (lift2 mulC (proj1 . proj1) (proj2 . proj2)) (lift2 mulC (proj2 . proj1) (proj1 . proj2))))
  negateC = FDiff (prod (negateC . proj1) (negateC . proj2))
  subC = lift2 addC proj1 (negateC . proj2)
  fromIntegerC n = FDiff (prod (fromIntegerC n) (fromIntegerC 0))

instance (Additive k, NumCat k a) => NumCat (RDiff k) a where
  addC = RDiff addC (prod (addC . proj1) (dup . proj2))
  mulC = RDiff mulC (prod (mulC . proj1)
    (prod (lift2 mulC (proj2 . proj1) proj2)
          (lift2 mulC (proj1 . proj1) proj2)))
  negateC = RDiff negateC (prod (negateC . proj1) (negateC . proj2))
  fromIntegerC n = RDiff (fromIntegerC n) (prod (fromIntegerC n) (zeroC . unit))

-- is this suspect?
instance (Cartesian k, Additive k) => Additive (RDiff k) where
  zeroC = RDiff zeroC (zeroC . unit)
  plusC = RDiff plusC $ prod (plusC . proj1) (dup . proj2)

instance (Cartesian k, Additive k) => Additive (FDiff k) where
  zeroC = FDiff (zeroC . unit)
  plusC = FDiff (prod (plusC . proj1) (plusC . proj2))



instance Cartesian (->) where
  dup = \x -> (x, x)
  proj1 = fst
  proj2 = snd
  prod = \f g x -> (f x, g x)
  unit = \_ -> ()

instance Num a => NumCat (->) a where
  addC = uncurry (+)
  mulC = uncurry (*)
  negateC = negate
  subC = uncurry (-)
  absC = abs
  signumC = signum
  fromIntegerC = fromInteger

instance Monad m => Cartesian (Kleisli m) where
  dup = arr $ \x -> (x, x)
  proj1 = arr fst
  proj2 = arr snd
  prod = \f g -> dup >>> f *** g
  unit = arr $ \_ -> ()

instance (Monad m, Num a) => NumCat (Kleisli m) a where
  addC = arr $ uncurry (+)
  mulC = arr $ uncurry (*)
  negateC = arr $ negate
  subC = arr $ uncurry (-)
  absC = arr abs
  signumC = arr signum
  fromIntegerC n = arr (\_ -> fromInteger n)


reverseDiff :: (Additive k, Cartesian k, NumCat k (Del a)) => RDiff k a a -> a `k` (a, Del a)
reverseDiff (RDiff f fd) = lift2 fd id (fromIntegerC 1)

forwardDiff :: (forall a k. NumCat k a => k a a) -> Double -> (Double, Double)
forwardDiff (FDiff f) x = f (x, 1)

forwardDiff2 :: (forall a k. NumCat k a => k a a) -> Double -> (Double, Double)
forwardDiff2 (FDiff (FDiff f)) x = (fx, xx)
  where
  ((fx, xy1), (xy2, xx)) = f ((x, 1), (1, 0))

reverseDiff' :: RDiff (Kleisli []) Double Double -> Double -> (Double, Del Double)
reverseDiff' (RDiff f fd) x = (fst (head xs), sum (map snd xs))
  where xs = runKleisli fd (x, 1)

reverseDiff'' :: (forall a k. NumCat k a => k a a) -> Double -> (Double, Double)
reverseDiff'' e = reverseDiff' e

-- Wrong wrong wrong!
reverseDiff2 :: (forall a k. NumCat k a => k a a) -> Double -> Double
reverseDiff2 (RDiff _ (RDiff _ fd)) x = head (map (snd . snd) xs)
  where xs = runKleisli fd ((x, 1), (0, 0))

reverseDiff1' :: (Cartesian k, Additive k, NumCat k (Del Double)) => Integer -> RDiff k Double Double -> k Double Double
reverseDiff1' i (RDiff f fd) = proj2 . lift2 fd id (fromIntegerC i)

reverseDiff2' :: (Cartesian k, Additive k, NumCat k (Del Double)) => RDiff (RDiff k) Double Double -> k Double Double
reverseDiff2' = reverseDiff1' 0 . reverseDiff1' 1