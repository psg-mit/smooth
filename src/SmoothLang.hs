module SmoothLang where

import Control.Arrow ((&&&))
import Prelude hiding (Real, max, min, Integral, (^))
import MPFR (Real)
import qualified Interval as I
import RealExpr (runPoint)
import FwdPSh (Additive, CPoint, R (..), (:=>) (..), (:*) (..), derivT, (#), dmap)
import Types.Real
import Types.Integral (Integral, mean, variance, uniform)
import FwdMode (getValue, VectorSpace)
import Rounded (ofString, RoundDir( Down ))
import Types.Maximizer (hausdorffDist, d_R2, Maximizer)
import qualified Types.Maximizer as M

dRealtoReal :: DReal () -> CPoint Real
dRealtoReal (R x) = getValue x

atPrec :: CPoint Real -> DReal () -> Real
atPrec err real = fst (head (filter f (runPoint (dRealtoReal real &&& err))))
  where f (i, erri) = I.upper (I.width 100 i) < I.lower erri

-- Section 1.1: the integral from 0 to 1 of the derivative of ReLU(x - 0.2)
-- Time: A stream that can be stopped with Ctrl + c
-- it takes <1 second to generate the results in the paper
-- Result:
-- [-1.0000000000, 0.00000000000]
-- [-0.5000000000000, 0.0000000000000]
-- [-0.50000000000000, -0.25000000000000]
-- [-0.5000000000000000, -0.3750000000000000]
-- [-0.43750000000000000, -0.37500000000000000]
-- [-0.4062500000000000000, -0.3750000000000000000]
-- [-0.40625000000000000000, -0.39062500000000000000]
-- [-0.4062500000000000000000, -0.3984375000000000000000]
reluIntegral :: DReal ()
reluIntegral =
  deriv (ArrD (\_ c -> (integral01 (ArrD (\wk x -> max 0 (x - (dmap wk c))))))) 0.6


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


-- Section 3.1: derivative of ReLU at 0
reluFirstDerivAt0 :: DReal ()
reluFirstDerivAt0 = deriv (ArrD (\_ x -> max 0 x)) 0

-- Time: <1 second
-- Result: [0.00000000000, 1.0000000000]
runReluFirstDerivAt0 :: Real
runReluFirstDerivAt0 = atPrec 2 reluFirstDerivAt0

-- Time: infinite (non-terminating)
-- Result: [0.00000000000, 1.0000000000]
runReluFirstDerivAt0nonterminating :: Real
runReluFirstDerivAt0nonterminating = atPrec 0.1 reluFirstDerivAt0

reluSquared :: DReal ()
reluSquared = deriv (ArrD (\_ x -> (max 0 x) * (max 0 x))) 0

-- Time: <1 second
-- Result: [0.00000000000, 0.00000000000]
runReluSquared :: Real
runReluSquared = atPrec 0.00001 reluSquared

reluIntegralDeriv :: DReal ()
reluIntegralDeriv =
  integral01 (ArrD (\_ -> deriv (ArrD (\_ x -> max 0 (x - 0.2)))))


-- Section 3.2: second derivative of cuberoot 8 example
secondDerivCuberoot8 ::  DReal ()
secondDerivCuberoot8 = second_deriv (ArrD (\_ -> cuberoot)) 8

-- Time: <1 second
-- Result: [-0.006944448713007772777947928, -0.006944443591540540717010462]
runSecondDerivCuberoot8 :: Real
runSecondDerivCuberoot8 = atPrec 0.00001 secondDerivCuberoot8


-- Section 3.2: derivative of f(x,y) = xy wrt x and y at (1,0)
secondDerivXY ::  DReal ()
secondDerivXY = deriv (ArrD (\_ x -> (deriv (ArrD (\wk y -> y * (dmap wk x))) 0))) 1

-- Time: <1 second
-- Result: [1.0000000000, 1.0000000000]
runSecondDerivXY :: Real
runSecondDerivXY = atPrec 0.00001 secondDerivXY


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

-- Time: 2 minutes
-- Result: [-0.004394948482513427734375, 0.004394948482513427734375]
runDerivVarianceLinearChange :: Real
runDerivVarianceLinearChange = atPrec 0.01 derivVarianceLinearChange

secondDerivVarianceLinearChange ::  DReal ()
secondDerivVarianceLinearChange =
  let ((y :* _) :* (_ :* dy2)) = derivT (ArrD (\_ -> derivT variance)) ((uniform :* change) :* (change :* (ArrD (\_ _ -> 0))))
  in dy2


--  Section 7.3: raytracing
dot :: VectorSpace g => (DReal :* DReal) g -> (DReal :* DReal) g -> DReal g
dot (x0 :* x1) (y0 :* y1) = x0 * y0 + x1 * y1

scale :: VectorSpace g => DReal g -> (DReal :* DReal) g -> (DReal :* DReal) g
scale c (x0 :* x1) = (c * x0) :* (c * x1)

normalize :: VectorSpace g => (DReal :* DReal) g -> (DReal :* DReal) g
normalize x@(x0 :* x1) = scale (1 / sqrt (x0^2 + x1^2)) x

gradient :: VectorSpace g => (DReal :* DReal :=> DReal) g -> (DReal :* DReal) g -> (DReal :* DReal) g
gradient f (x0 :* x1) =
  (deriv (ArrD $ \wk z -> dmap wk f # (z :* dmap wk x0)) x0) :* (deriv (ArrD $ \wk z -> dmap wk f # (dmap wk x1 :* z)) x0)

raytrace :: VectorSpace g => ((DReal :* DReal) :=> DReal) g ->
                             (DReal :* DReal) g ->
                             (DReal :* DReal) g -> DReal g
raytrace s lightPos u =
  let t = firstRoot (ArrD (\wk t -> dmap wk s # (scale t (dmap wk u)))) in
  let y = scale t u in
  let normal = gradient s y in
  max 0 (dot (normalize normal) (normalize (lightPos `sub` y)))
  where
  (x0 :* x1) `sub` (y0 :* y1) = (x0 - y0) :* (x1 - y1)

circle :: VectorSpace g => DReal g -> ((DReal :* DReal) :=> DReal) g
circle y0 = ArrD $ \wk (x :* y) -> 1 - ((x - 1)^2 + (y - dmap wk y0)^2)

rayTrace :: DReal ()
rayTrace = raytrace (circle (-3/4)) (1 :* 1) (1 :* 0)

rayTraceDeriv :: DReal ()
rayTraceDeriv = deriv (ArrD (\_ y0 -> raytrace (circle y0) (1 :* 1) (1 :* 0))) (-3/4)

-- Time: <1 second
-- Result: [0.14141667894924812184427172108378768467, 0.14142297467777446020890677629582431684]
runRayTrace :: Real
runRayTrace = atPrec 0.00001 rayTrace

-- Time: 20 seconds
-- Result: [1.836082661248419481260195175334, 1.836741944317042477214026217507]
runRayTraceDeriv :: Real
runRayTraceDeriv = atPrec 0.001 rayTraceDeriv


-- Section 7.4: Hausdorff distance between quarter-circle and L-shape.
quarter_circle :: VectorSpace g => DReal g -> Maximizer (DReal :* DReal) g
quarter_circle y0 = M.map (ArrD (\wk theta -> let y0' = dmap wk y0 in
  (cos (pi / 2 * theta)) :* (y0' + sin (pi / 2 * theta)))) M.unit_interval

quarter_square_perim :: VectorSpace g => Maximizer (DReal :* DReal) g
quarter_square_perim = M.union (M.map (ArrD (\_ x -> x :* 1)) M.unit_interval)
                               (M.map (ArrD (\_ y -> 1 :* y)) M.unit_interval)

hausdorffDistCircleL ::  DReal ()
hausdorffDistCircleL = hausdorffDist d_R2 quarter_square_perim (quarter_circle 0)

-- Time: 7 seconds
-- Result: [0.41384921849465670653300003702, 0.41440539111235744884709353399]
runHausdorffDistCircleL :: Real
runHausdorffDistCircleL = atPrec 0.001 hausdorffDistCircleL


-- Section 7.4: derivative of Hausdorff distance between quarter-circle and L-shape wrt. translation.
hausdorffDistTranslatedQuarterCircle :: DReal ()
hausdorffDistTranslatedQuarterCircle =
  deriv (ArrD (\_ y -> hausdorffDist d_R2 quarter_square_perim (quarter_circle y))) 0

-- Time: 10 minutes
-- Result: [-0.752, -0.664]
runHausdorffDistTranslatedQuarterCircle :: Real
runHausdorffDistTranslatedQuarterCircle = atPrec 0.1 hausdorffDistTranslatedQuarterCircle
