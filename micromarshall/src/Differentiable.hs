{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving, RankNTypes #-}
{-# LANGUAGE TypeOperators, TypeFamilies, FlexibleContexts #-}
module Differentiable where

import Lib
import Control.Category
import Prelude hiding (id, (.))

import Unsafe.Coerce (unsafeCoerce)

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

-- instance Cartesian k => Cartesian (RDiff k) where
--   dup = RDiff dup (prod (dup . proj1) (plusC . proj2))
--   proj1 = RDiff proj1 (prod (proj1 . proj1) (prod id (zeroC . unit) . proj2))
--   proj2 = RDiff proj2 (prod (proj2 . proj1) (prod (zeroC . unit) id . proj2))
--   prod (RDiff f fd) (RDiff g gd) = RDiff (prod f g)
--     (prod (prod (proj1 . proj1) (proj1 . proj2)) (lift2' plusC (proj2 . proj1) (proj2 . proj2)) .
--      prod (lift2' fd proj1 (proj1 . proj2)) (lift2' gd proj1 (proj2 . proj2))
--     )
--   unit = RDiff unit (prod unit (zeroC . unit))

instance NumCat k a => NumCat (FDiff k) a where
  addC = FDiff (prod (addC . proj1) (addC . proj2))
  mulC = FDiff (prod (mulC . proj1) (lift2' addC (lift2' mulC (proj1 . proj1) (proj2 . proj2)) (lift2' mulC (proj2 . proj1) (proj1 . proj2))))
  negateC = FDiff (prod (negateC . proj1) (negateC . proj2))
  subC = lift2' addC proj1 (negateC . proj2)

-- instance (Additive k a, NumCat k a) => NumCat (RDiff k) a where
--   addC = RDiff addC (prod (addC . proj1) (dup . proj2))
--   mulC = RDiff mulC (prod (mulC . proj1)
--     (prod (lift2' mulC (proj2 . proj1) proj2)
--           (lift2' mulC (proj1 . proj1) proj2)))
--   negateC = RDiff negateC (prod (negateC . proj1) (negateC . proj2))


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


reverseDiff :: (Additive k a, Cartesian k, NumCat k (Del a)) => RDiff k a a -> a `k` (a, Del a)
reverseDiff (RDiff f fd) = fd . prod id (fromIntegerC 1)

forwardDiff :: (forall a k. NumCat k a => k a a) -> Double -> (Double, Double)
forwardDiff (FDiff f) x = f (x, 1)

-- reverseDiff' :: RDiff (->) Double Double -> Double -> (Double, Double)
-- reverseDiff' e = reverseDiff e

-- reverseDiff'' :: (forall a k. NumCat k a => k a a) -> Double -> (Double, Double)
-- reverseDiff'' e = reverseDiff e