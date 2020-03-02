module SmoothLang where

import Prelude hiding (Real, max, min)
import MPFR (Real)
import qualified Interval as I
import RealExpr (runPoint)
import FwdPSh (Additive, CPoint, R (..), (:=>) (..), max, wkn, integral, getDerivTower', (:*) (..), derivT)
import Types.Real (DReal, cuberoot, deriv, second_deriv)
import Types.Integral (mean, variance, uniform, change)
import FwdMode (getValue)
import Rounded (ofString, RoundDir( Down ))
import Types.Maximizer (hausdorffDist, d_R2, quarter_square_perim, quarter_circle)

dRealtoReal :: DReal () -> CPoint Real
dRealtoReal (R x) = getValue x

atPrec :: Double -> CPoint Real -> Real
atPrec err real = let err' = ofString 100 Down (show err) in
  (filter (\i -> (I.upper (I.width 100 i)) < err') (runPoint real)) !! 0

-- Section 3: cuberoot 2
cuberoot2 :: CPoint Real
cuberoot2 = dRealtoReal (cuberoot 2)

-- Section 3: derivative of cuberoot 8 example
oneTwelfth :: CPoint Real
oneTwelfth = 1 / 12

cuberoot8 :: CPoint Real
cuberoot8 = dRealtoReal $ deriv (ArrD (\_ -> cuberoot)) 8

-- Section 3.1: derivative of ReLU at 0
reluDerivTower :: CPoint Real -> Int -> CPoint Real
reluDerivTower x n = getDerivTower' (max 0) x !! n

reluFirstDerivAt0 :: CPoint Real
reluFirstDerivAt0 = reluDerivTower 0 1

-- Section 3.1: the integral from 0 to 1 of the derivative of ReLU(x - 0.2)
-- TODO
-- reluIntegralDerivTower :: CPoint Real
-- reluIntegralDerivTower =
--   integral (\x -> (getDerivTower' (\x -> max 0 (x - wkn 0.2)) x) !! 1)

-- Section 3.2: second derivative of cuberoot 8 example
secondDerivCuberoot8 :: CPoint Real
secondDerivCuberoot8 = dRealtoReal $ second_deriv (ArrD (\_ -> cuberoot)) 8

-- Section 6.1: Ignoring for now because of liklihood of future changes
-- TODO

-- Section 7.1.3: derivative of the mean of a uniform distribution wrt. a line perturbation
derivMeanLinearChange :: CPoint Real
derivMeanLinearChange = let (y :* dy) = derivT mean (uniform :* change) in dRealtoReal dy

-- Section 7.1.3: derivative of the variance of a uniform distribution wrt. a line perturbation
derivVarianceLinearChange :: CPoint Real
derivVarianceLinearChange = let (y :* dy) = derivT variance (uniform :* change) in dRealtoReal dy

-- Section 7.4: hausdorff dist between quarter-circle and L-shape.
hausdorffDistCircleL :: CPoint Real
hausdorffDistCircleL = dRealtoReal $ hausdorffDist d_R2 quarter_square_perim (quarter_circle 1)

-- Section 7.4: derivative of hausdorff dist between quarter-circle and L-shape wrt. radius.
exampleHausdorffDist3Deriv :: CPoint Real
exampleHausdorffDist3Deriv =
  dRealtoReal $ deriv (ArrD (\_ r -> hausdorffDist d_R2 quarter_square_perim (quarter_circle r))) 1
