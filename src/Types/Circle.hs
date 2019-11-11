{-# LANGUAGE TypeOperators #-}

module Types.Circle where

import Prelude hiding (Real)
import FwdMode ((:~>), pairD, fstD, sndD)
import FwdPSh
import MPFR (Real)

data Circle g = Circle (DReal g) (DReal g)

fromAngle :: DReal g -> Circle g
fromAngle theta = Circle (cos theta) (sin theta)

rotate :: DReal g -> Circle g -> Circle g
rotate theta (Circle x y) = Circle (cos theta * x + sin theta * y)
                                   (cos theta * y - sin theta * x)

toXY :: Circle g -> (DReal :* DReal) g
toXY (Circle x y) = x :* y

-- Point on circle plus change in angle to tangent bundle
toTan :: Circle g -> DReal g -> Tan Circle g
toTan (Circle (R x) (R y)) (R dtheta) = Tan (pairD (pairD x y) (pairD dx dy))
  (Circle (R fstD) (R sndD))
  where
  dx = -y * dtheta
  dy =  x * dtheta

-- From tangent bundle to point on circle plus angle
fromTan :: Tan Circle g -> (Circle :* DReal) g
fromTan (Tan udu (Circle x' y')) = Circle x y :* theta  where
  xdx :* ydy = tanProdfrom (Tan udu (x' :* y'))
  x :* dx = tanRfrom xdx
  y :* dy = tanRfrom ydy
  theta = x * dy - y * dx

-- The exponential map for the circle
exponentialMap :: Tan Circle g -> Circle g
exponentialMap t = rotate theta (Circle x y) where
  Circle x y :* theta = fromTan t