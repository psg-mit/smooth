{-# LANGUAGE TypeFamilies, UndecidableSuperClasses, FlexibleContexts, TypeApplications, FlexibleInstances #-}
-- {-# LANGUAGE UndecidableInstances #-}

module Tangent where

class (VectorBundle (Tangent a), Smooth (Tangent a)) => Smooth a where
  type Tangent a :: *
  value :: Tangent a -> a

-- instance (Smooth a, Smooth b) => Smooth (a, b) where
--   type Tangent (a, b) = (Tangent a, Tangent b)
--   value (tx, ty) = (value tx, value ty)

-- instance (Smooth a, Smooth b) => Smooth (Either a b) where
--   type Tangent (Either a b) = Either (Tangent a) (Tangent b)
--   value (Left x) = Left (value x)
--   value (Right y) = Right (value y)

-- instance Smooth Double where
--   type Tangent Double = (Double, Double)
--   value = fst

data SmoothF a b = SmoothF
  { eval :: a -> b
  , withDeriv :: SmoothF (Tangent a) (Tangent b)
  }

class VectorSpace a where
  vzero :: a
  vplus :: a -> a -> a

class VectorBundle a where
  vbplus :: a -> a -> a

-- instance (VectorBundle a, VectorBundle b) => VectorBundle (a, b) where
--   vbplus (xa, xb) (ya, yb) = vbplus (xa, ya) (xb, yb)

sid :: Smooth a => SmoothF a a
sid = SmoothF id sid

-- SmoothF (Tangent Double, Tangent Double) (Tangent Double)

instance VectorSpace Double where
  vzero = 0
  vplus = (+)

-- instance VectorSpace a => VectorBundle a where
--   vbplus = vplus

-- splus :: SmoothF (Double, Double) Double
-- splus = SmoothF (uncurry (+)) (

-- sproj1 :: Smooth a => Smooth b => SmoothF (a, b) a
-- sproj1 = SmoothF fst sproj1

-- sproj2 :: Smooth a => Smooth b => SmoothF (a, b) a
-- sproj2 = SmoothF fst sproj2

-- sdup :: Smooth a => SmoothF a (a, a)
-- sdup = SmoothF (\x -> (x, x)) sdup

-- smul :: SmoothF (Double, Double) Double
-- smul = SmoothF (uncurry (*)) (