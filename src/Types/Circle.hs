{-# LANGUAGE TypeOperators #-}

module Types.Circle where

import Prelude hiding (Real)
import FwdMode ((:~>), pairD, fstD, sndD, dId)
import FwdPSh
import MPFR (Real)


-- Circle = Real quotiented by the equivalence relation
-- x ~ y := x - y = 2 * k * pi  for some integer k
-- Equivalently, implementing the Circle as the
-- coimage of `cossin : R -> R^2`
newtype Circle g = FromAngle (DReal g)

fromAngle :: DReal g -> Circle g
fromAngle = FromAngle

toXY :: Circle g -> (DReal :* DReal) g
toXY (FromAngle theta) = cos theta :* sin theta

rotate :: DReal g -> Circle g -> Circle g
rotate deltaTheta (FromAngle theta) = FromAngle (theta + deltaTheta)

-- The tangent bundle for the circle is just
-- a point on the circle plus a change in angle
tangent :: Tan Circle g :== (Circle :* DReal) g
tangent = Bijection fromTan toTan where
  toTan (FromAngle (R theta) :* R dtheta) =
    Tan (pairD theta dtheta) (FromAngle (R dId))
  fromTan (Tan udu (FromAngle f)) = FromAngle theta :* dtheta where
    theta :* dtheta = from tanR (Tan udu f)

-- The exponential map for the circle
exponentialMap :: Tan Circle g -> Circle g
exponentialMap t = rotate dtheta (FromAngle theta) where
  FromAngle theta :* dtheta = from tangent t