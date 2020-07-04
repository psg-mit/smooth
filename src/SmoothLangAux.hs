module SmoothLangAux where

import Prelude hiding (Real, max, min, Integral, (^))
import FwdPSh (Additive, CPoint, R (..), (:=>) (..), (:*) (..), derivT, (#), dmap)
import SmoothLang
import Types.Real
import MPFR (Real)


-- Section 3: cuberoot 2
cuberoot2 :: DReal ()
cuberoot2 = cuberoot 2

-- Time: <1 second
-- Result: [1.259921044, 1.259921059]
runCuberoot2 :: Real
runCuberoot2 = atPrec 0.00001 cuberoot2


-- Section 3: derivative of cuberoot 8 example
derivCuberoot8 ::  DReal ()
derivCuberoot8 = deriv (ArrD (\_ -> cuberoot)) 8

-- Time: <1 second
-- Result: [0.08333333275125672724797760, 0.08333335031057036046674712]
runDerivCuberoot8 :: Real
runDerivCuberoot8 = atPrec 0.00001 derivCuberoot8

derivReluSquared :: DReal ()
derivReluSquared = deriv (ArrD (\_ x -> (max 0 x) * (max 0 x))) 0

-- Time: <1 second
-- Result: [0.00000000000, 0.00000000000]
runDerivReluSquared :: Real
runDerivReluSquared = atPrec 0.00001 derivReluSquared

reluIntegralDeriv :: DReal ()
reluIntegralDeriv =
  integral01 (ArrD (\_ -> deriv (ArrD (\_ x -> max 0 (x - 0.2)))))

-- Time: 1 minute
-- Result: [0.79999542, 0.80000305]
runReluIntegralDeriv :: Real
runReluIntegralDeriv = atPrec 0.00001 reluIntegralDeriv

-- Section 3.2: second derivative of cuberoot 8 example
secondDerivCuberoot8 ::  DReal ()
secondDerivCuberoot8 = second_deriv (ArrD (\_ -> cuberoot)) 8

-- Time: <1 second
-- Result: [-0.006944448713007772777947928, -0.006944443591540540717010462]
runSecondDerivCuberoot8 :: Real
runSecondDerivCuberoot8 = atPrec 0.00001 secondDerivCuberoot8


-- Section 3.2: derivative of f(x,y) = xy wrt x and y at (1,0)
mixedPartialXY ::  DReal ()
mixedPartialXY = deriv (ArrD (\_ x -> (deriv (ArrD (\wk y -> y * (dmap wk x))) 0))) 1

-- Time: <1 second
-- Result: [1.0000000000, 1.0000000000]
runMixedPartialXY :: Real
runMixedPartialXY = atPrec 0.00001 mixedPartialXY