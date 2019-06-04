{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Lib where

import Control.Category
import Prelude hiding (id, (.))

someFunc :: IO ()
someFunc = putStrLn "someFunc"

class Cartesian k => NumCat k a where
  addC :: (a, a) `k` a
  mulC :: (a, a) `k` a
  negateC :: a `k` a
  negateC = subC . prod (fromIntegerC 0) id
  subC :: (a, a) `k` a
  subC = addC . prod (id . proj1) (negateC . proj2)
  absC :: a `k` a
  signumC :: a `k` a
  fromIntegerC :: Integer -> g `k` a


instance (Cartesian k, NumCat k a) => Num (g `k` a) where
  (+) = lift2' addC
  (*) = lift2' mulC
  abs = lift1' absC
  (-) = lift2' subC
  negate = lift1' negateC
  signum = lift1' signumC
  fromInteger = fromIntegerC

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

lift1' :: Category k => (a `k` b) -> g `k` a -> g `k` b
lift1' f x = f . x

lift2' :: Cartesian k => ((a, b) `k` c) -> g `k` a -> g `k` b -> g `k` c
lift2' f x y = f . prod x y

unlift2' :: Cartesian k => (forall g. g `k` a -> g `k` b -> g `k` c) -> (a, b) `k` c
unlift2' f = f proj1 proj2

matchPair :: Cartesian k => g `k` (a, b) -> (forall d. Extends k g d => d `k` a -> d `k` b -> d `k` c) -> g `k` c
matchPair p f = f (proj1 . p) (proj2 . p)

quantifier :: Cartesian k => (forall g. (g, a) `k` b -> g `k` b) -> forall g. (forall d. Extends k g d => d `k` a -> d `k` b) -> g `k` b
quantifier quant f = quant (f proj2)