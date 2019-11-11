{-# LANGUAGE TypeOperators #-}

module Types.Circle where

import Prelude hiding (Real)
import FwdMode ((:~>), pairD, fstD, sndD, dId)
import FwdPSh
import MPFR (Real)


-- Circle = Real quotiented by the equivalence relation
-- x ~ y := x - y = 2 * k * pi  for some integer k
newtype Circle g = Circle (DReal g)

fromAngle :: DReal g -> Circle g
fromAngle theta = Circle theta

rotate :: DReal g -> Circle g -> Circle g
rotate deltaTheta (Circle theta) = Circle (theta + deltaTheta)

toXY :: Circle g -> (DReal :* DReal) g
toXY (Circle theta) = cos theta :* sin theta

-- Point on circle plus change in angle to tangent bundle
toTan :: Circle g -> DReal g -> Tan Circle g
toTan (Circle (R theta)) (R dtheta) = Tan (pairD theta dtheta) (Circle (R dId))

-- From tangent bundle to point on circle plus angle
fromTan :: Tan Circle g -> (Circle :* DReal) g
fromTan (Tan udu (Circle f)) = Circle theta :* dtheta where
  theta :* dtheta = tanRfrom (Tan udu f)

-- The exponential map for the circle
exponentialMap :: Tan Circle g -> Circle g
exponentialMap t = rotate dtheta (Circle theta) where
  Circle theta :* dtheta = fromTan t