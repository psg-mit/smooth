{-# LANGUAGE TypeFamilies #-}

module Types.CircleS where

import Prelude hiding (Real)
import FwdMode ((:~>), pairD, fstD, sndD, VectorSpace)
import FwdPSh
import MPFR (Real)


-- Circle = { (x, y) : R^2 | x^2 + y^2 = 1 }
-- Equivalently, implementing the Circle as the
-- image of `cossin : R -> R^2`
newtype Circle g = Circle {
  toXY :: (DReal :* DReal) g
  }

fromAngle :: DReal g -> Circle g
fromAngle theta = Circle (cos theta :* sin theta)

rotate :: DReal g -> Circle g -> Circle g
rotate theta (Circle (x :* y)) = Circle $
     (cos theta * x + sin theta * y)
  :* (cos theta * y - sin theta * x)

-- The tangent bundle for the circle is just
-- a point on the circle plus a change in angle
instance Tangential Circle where
  type Tangent Circle = Circle :* DReal
  -- tangent :: Tan Circle g :== (Circle :* DReal) g
  tangent = Bijection fromTan toTan where
    fromTan (Tan udu (Circle (x' :* y'))) = Circle (x :* y) :* theta  where
      xdx :* ydy = from tanProd (Tan udu (x' :* y'))
      x :* dx = from tanR xdx
      y :* dy = from tanR ydy
      theta = x * dy - y * dx
    toTan (Circle (R x :* R y) :* R dtheta) = Tan (pairD (pairD x y) (pairD dx dy))
      (Circle (R fstD :* R sndD))
      where
      dx = -y * dtheta
      dy =  x * dtheta


-- The exponential map for the circle
exponentialMap :: VectorSpace g => Tan Circle g -> Circle g
exponentialMap t = rotate theta (Circle xy) where
  Circle xy :* theta = from tangent t