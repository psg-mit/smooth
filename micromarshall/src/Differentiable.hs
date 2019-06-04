{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
module Differentiable where

import Lib

type Dual a = (a, a)

instance NumCat k a => NumCat k (Dual a) where
  addC = unlift2' (\xdx ydy -> matchPair xdx (\x dx -> matchPair (lift ydy) (\y dy -> prod (lift x + y) (lift dx + dy))))
  mulC = unlift2' (\xdx ydy -> matchPair xdx (\x dx -> matchPair (lift ydy) (\y dy -> prod (lift x * y) (lift dx * y + lift x * dy))))
  -- mulC :: (a, a) `k` a
  -- negateC :: a `k` a
  -- negateC = subC . prod (fromIntegerC 0) id
  -- subC :: (a, a) `k` a
  -- subC = addC . prod (id . proj1) (negateC . proj2)
  -- absC :: a `k` a
  -- signumC :: a `k` a
  -- fromIntegerC :: Integer -> g `k` a