module SmoothLang where

import Control.Arrow ((&&&))
import Prelude hiding (Real, max, min, Integral)
import MPFR (Real)
import qualified Interval as I
import RealExpr (runPoint)
import FwdPSh (Additive, CPoint, R (..), (:=>) (..), (:*) (..), derivT, (#), dmap)
import Types.Real
import Types.Integral (Integral, mean, variance, uniform)
import FwdMode (getValue)
import Rounded (ofString, RoundDir( Down ))
import Types.Maximizer (hausdorffDist, d_R2, quarter_square_perim, quarter_circle)

dRealtoReal :: DReal () -> CPoint Real
dRealtoReal (R x) = getValue x

atPrec :: CPoint Real -> DReal () -> Real
atPrec err real = fst (head (filter f (runPoint (dRealtoReal real &&& err))))
  where f (i, erri) = I.upper (I.width 100 i) < I.lower erri

-- Section 3: cuberoot 2
cuberoot2 :: DReal ()
cuberoot2 = cuberoot 2

-- Time: immediate
-- Result: [1.2596970, 1.2599339]
runCuberoot2 :: Real
runCuberoot2 = atPrec 0.01 cuberoot2


-- Section 3: derivative of cuberoot 8 example
oneTwelfth ::  DReal ()
oneTwelfth = 1 / 12

-- Time: immediate
-- Result: [0.083333333314, 0.083333333343]
runOneTwelfth :: Real
runOneTwelfth = atPrec 0.01 oneTwelfth

derivCuberoot8 ::  DReal ()
derivCuberoot8 = deriv (ArrD (\_ -> cuberoot)) 8

-- Time: immediate
-- Result: [0.08207671663416818358555, 0.09196111422526140110103]
runDerivCuberoot8 :: Real
runDerivCuberoot8 = atPrec 0.01 derivCuberoot8


-- Section 3.1: derivative of ReLU at 0
reluFirstDerivAt0 :: DReal ()
reluFirstDerivAt0 = deriv (ArrD (\_ x -> max 0 x)) 0

-- Time: immediate
-- Result: [0.00000000000, 1.0000000000]
runReluFirstDerivAt0 :: Real
runReluFirstDerivAt0 = atPrec 2 reluFirstDerivAt0


-- Section 3.1: the integral from 0 to 1 of the derivative of ReLU(x - 0.2)
reluIntegralDeriv :: DReal ()
reluIntegralDeriv =
  integral01 (ArrD (\_ -> deriv (ArrD (\_ x -> max 0 (x - 0.2)))))

-- Time: immediate
-- Result: [0.79687500, 0.80468750]
runReluIntegralDeriv :: Real
runReluIntegralDeriv = atPrec 0.01 reluIntegralDeriv


-- Section 3.2: second derivative of cuberoot 8 example
secondDerivCuberoot8 ::  DReal ()
secondDerivCuberoot8 = second_deriv (ArrD (\_ -> cuberoot)) 8

-- Time: immediate
-- Result: [-0.0069805319281614268773525, -0.0069361180547353969938394]
runSecondDerivCuberoot8 :: Real
runSecondDerivCuberoot8 = atPrec 0.001 secondDerivCuberoot8

-- Section 6.1: Ignoring for now because of liklihood of future changes
-- TODO


-- Section 7.1.3: derivative of the mean of a uniform distribution wrt. a line perturbation
change :: Integral DReal g
change = ArrD $ \_ f -> uniform # (ArrD (\wk x -> (x - 1/2) * dmap wk f # x))

derivMeanLinearChange ::  DReal ()
derivMeanLinearChange = let y :* dy = derivT mean (uniform :* change) in dy

-- Time: 2 seconds
-- Result: [0.082967042922973632812500000, 0.083699464797973632812500000]
runDerivMeanLinearChange :: Real
runDerivMeanLinearChange = atPrec 0.001 derivMeanLinearChange


-- Section 7.1.3: derivative of the variance of a uniform distribution wrt. a line perturbation
derivVarianceLinearChange ::  DReal ()
derivVarianceLinearChange = let y :* dy = derivT variance (uniform :* change) in dy

-- Time: 1 second
-- Result: [-0.035369873046875000, 0.035369873046875000]
runDerivVarianceLinearChange :: Real
runDerivVarianceLinearChange = atPrec 0.1 derivVarianceLinearChange


-- Section 7.4: hausdorff dist between quarter-circle and L-shape.
hausdorffDistCircleL ::  DReal ()
hausdorffDistCircleL = hausdorffDist d_R2 quarter_square_perim (quarter_circle 1)

-- Time: 7 seconds
-- Result: [0.41384921849465670653300003702, 0.41440539111235744884709353399]
runHausdorffDistCircleL :: Real
runHausdorffDistCircleL = atPrec 0.001 hausdorffDistCircleL


-- Section 7.4: derivative of hausdorff dist between quarter-circle and L-shape wrt. radius.
exampleHausdorffDist3Deriv :: DReal ()
exampleHausdorffDist3Deriv =
  deriv (ArrD (\_ r -> hausdorffDist d_R2 quarter_square_perim (quarter_circle r))) 1