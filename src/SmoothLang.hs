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

-- Section 1: the integral from 0 to 1 of the derivative of ReLU(x - c) at c=0.6
derivIntegralRelu :: DReal ()
derivIntegralRelu =
  deriv (ArrD (\_ c -> (integral01 (ArrD (\wk x -> max 0 (x - (dmap wk c))))))) 0.6

-- Time: <1 second
-- Result: [-0.4062500000000000000000, -0.3984375000000000000000]
runDerivIntegralRelu :: Real
runDerivIntegralRelu = atPrec 1e-2 derivIntegralRelu

-- Section 2: raytracing
dot :: VectorSpace g => (DReal :* DReal) g -> (DReal :* DReal) g -> DReal g
dot (x0 :* x1) (y0 :* y1) = x0 * y0 + x1 * y1

scale :: VectorSpace g => DReal g -> (DReal :* DReal) g -> (DReal :* DReal) g
scale c (x0 :* x1) = (c * x0) :* (c * x1)

norm2 :: (DReal :* DReal) g -> DReal g
norm2 (x :* y) = x^2 + y^2

normalize :: VectorSpace g => (DReal :* DReal) g -> (DReal :* DReal) g
normalize x = scale (1 / sqrt (norm2 x)) x

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
  let lightVector = lightPos `sub` y in
  max 0 (dot (normalize normal) (normalize lightVector))
  / (norm2 y * norm2 lightVector)
  where
  (x0 :* x1) `sub` (y0 :* y1) = (x0 - y0) :* (x1 - y1)

circle :: VectorSpace g => DReal g -> ((DReal :* DReal) :=> DReal) g
circle y0 = ArrD $ \wk (x :* y) -> ((x - 1)^2 + (y - dmap wk y0)^2) - 1

raytraceExample :: DReal ()
raytraceExample = raytrace (circle (-3/4)) (1 :* 1) (1 :* 0)

raytraceExampleDeriv :: DReal ()
raytraceExampleDeriv = deriv (ArrD (\_ y0 -> raytrace (circle y0) (1 :* 1) (1 :* 0))) (-3/4)

-- Time: 1 second
-- Result: [2.587289929104514485486379588564089986615867, 2.587298566457847103838396428782456969483227]
runRaytraceExample :: Real
runRaytraceExample = atPrec 1e-5 raytraceExample

-- Time: 12 seconds
-- Result: [1.347739015144645601713439374053190179150, 1.348337596821412823551715548182238961320]
runRaytraceExampleDeriv :: Real
runRaytraceExampleDeriv = atPrec 1e-3 raytraceExampleDeriv

-- Section 2.1
tStar :: VectorSpace g => DReal g -> DReal g
tStar y = firstRoot (ArrD (\wk t -> - (1 - dmap wk y^2 - (t - 1)^2)))

derivTStar :: VectorSpace g => DReal g -> DReal g
derivTStar y = deriv (ArrD (\_ -> tStar)) y

derivTStarAnalytic :: VectorSpace g => DReal g -> DReal g
derivTStarAnalytic y = - y / (tStar y - 1)

-- Time: <1 second
-- Result: [-1.133899683374569614339844628613941903, -1.133893143859001568699824674725477525]
runDerivTStar :: Real
runDerivTStar = atPrec 1e-5 (derivTStar (-3/4))

-- Time: <1 second
-- Result: [-1.133899683374569614339844628613941903, -1.133893143859001568699824674725477525]
runDerivTStarAnalytic :: Real
runDerivTStarAnalytic = atPrec 1e-5 (derivTStarAnalytic (-3/4))

-- Section 2.3: derivative of ReLU at 0
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

brightness :: VectorSpace g => DReal g -> DReal g
brightness y = integral01 (ArrD (\wk y0 -> max 0 ((y0 - dmap wk y) / sqrt (1 + (y0 - dmap wk y)^2))))

-- Time: ~4 seconds
-- Result: [-0.44750046730041503906250000000, -0.44692683219909667968750000000]
runDerivBrightness :: Real
runDerivBrightness = atPrec 1e-3 (deriv (ArrD (\_ -> brightness)) (1/2))


-- Section 6:
sqrt2 :: DReal ()
sqrt2 = sqrt 2

sqrt2Squared ::  DReal ()
sqrt2Squared = (sqrt 2)^2

two :: DReal ()
two = 2


-- Section 6.1: derivative of the mean of a uniform distribution wrt. a line perturbation
change :: Integral DReal g
change = ArrD $ \_ f -> uniform # (ArrD (\wk x -> (x - 1/2) * dmap wk f # x))

derivMeanLinearChange ::  DReal ()
derivMeanLinearChange = let y :* dy = derivT mean (uniform :* change) in dy

-- Time: 2 seconds
-- Result: [0.082967042922973632812500000, 0.083699464797973632812500000]
runDerivMeanLinearChange :: Real
runDerivMeanLinearChange = atPrec 0.001 derivMeanLinearChange


-- Section 6.1: derivative of the variance of a uniform distribution wrt. a line perturbation
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



-- Section 6.3: Hausdorff distance between quarter-circle and L-shape.
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


-- Section 6.3: derivative of Hausdorff distance between quarter-circle and L-shape wrt. translation.
hausdorffDistTranslatedQuarterCircle :: DReal ()
hausdorffDistTranslatedQuarterCircle =
  deriv (ArrD (\_ y -> hausdorffDist d_R2 quarter_square_perim (quarter_circle y))) 0

-- Time: 52 seconds
-- Result: [-0.752, -0.664]
runHausdorffDistTranslatedQuarterCircle :: Real
runHausdorffDistTranslatedQuarterCircle = atPrec 0.1 hausdorffDistTranslatedQuarterCircle
