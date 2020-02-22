{-# LANGUAGE RankNTypes #-}

module Types.Discrete where

import Prelude hiding (Real)
import FwdMode ((:~>), pairD, fstD, sndD, dId, (@.), bang, getValue)
import FwdPSh hiding (fromCPoint)
import qualified FwdPSh as F
import qualified Control.Category as C
import RealExpr (CMap)

newtype Box a g = Box (a ())

flat :: PShD a => Additive g => Box a g -> a g
flat (Box x) = dmap bang x

boxbox :: Box (Box a) g :== Box a g
boxbox = Bijection f g where
  f (Box (Box x)) = Box x
  g (Box x) = Box (Box x)

point :: Point a :== Box (R D a) g
point = Bijection f g where
  f x = Box (R x)
  g (Box (R x)) = x

cPoint :: Additive a => CPoint a :== Box (R D a) g
cPoint = Bijection f g where
  f = from point . F.fromCPoint
  g = getValue . to point

-- there is no tangent space: the tangent bundle consists only of the value
tangent :: Tan (Box a) g :== Box a g
tangent = Bijection f g where
  f (Tan xdx (Box y)) = Box y
  g (Box x) = (Tan (pairD bang bang) (Box x))

-- You only need a function on values to implement the function
fromFunction :: Additive a => Additive b => (CPoint a -> CPoint b) -> Box (R D a) g -> Box (R D b) g
fromFunction f x = from cPoint (f (to cPoint x))

fromCMap :: Additive a => Additive b => CMap a b -> Box (R D a) g -> Box (R D b) g
fromCMap f = fromFunction (f C..)

map :: PShD a => Box (a :=> b) g -> Box a g -> Box b g
map (Box (ArrD f)) (Box x) = Box (f dId (dmap bang x))