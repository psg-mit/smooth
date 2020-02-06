module SmoothLang where

import Prelude (snd)
import Control.Arrow ((&&&), (<<<), arr)
import Expr
import RealExpr (B, runPoint, CPoint)
import qualified RealExpr as RE
import MPFR (Real, firstRoot, firstRoot1, RootResult)
import Rounded (Rounded)
import Data.Bool( Bool( True ) )

sqrt2Example :: CPoint Real
sqrt2Example = dedekind_cut (\x -> x < 0 || (x ^ 2) < 2)

sqrt2Example' :: CPoint Real
sqrt2Example' = dedekind_cut1 (arr snd < 0 || (arr snd ^ 2) < 2)

quantificationExample :: CPoint Bool
quantificationExample = exists_unit_interval (\x -> isTrue (x < asMPFR 0.5 && x > 0.3))

newtonSqrt2Example :: CPoint Real
newtonSqrt2Example = newton_cut (\x -> max (-x) (2 - x^2) &&& ap1 RE.max_deriv ((-x &&& (2 - x^2)) &&& (-1 &&& -2*x)))

f :: Interval MPFR -> B
f x = (True, True)

firstRootExample :: CPoint RootResult
firstRootExample = firstRoot <<< arr (\() -> f)

-- Approaches 0.5 as is correct
firstRootInTheMiddle :: CPoint RootResult
firstRootInTheMiddle = firstRoot1 (arr snd < 0 || (arr snd ^ 2) < 0.25)

-- biddle :: CPoint Real
-- biddle = firstRoot1 ((arr snd - 1.1) < 0)

-- -- Should go to zero?
-- firstRootOfDoublePM :: CPoint Real
-- firstRootOfDoublePM = firstRoot1 (arr snd < 0 || ((arr snd - asMPFR 0.3) * (arr snd - asMPFR 0.7) < 0))

-- -- Should go to 0.3
-- firstRootOfDoubleMP :: CPoint Real
-- firstRootOfDoubleMP = firstRoot1 (arr snd < 0 || ((arr snd - asMPFR 0.3) * (arr snd - asMPFR 0.7) > 0))

-- firstRootBoundaryLeft :: CPoint Real
-- firstRootBoundaryLeft = firstRoot1 (arr snd < 0 || ((arr snd - asMPFR 0.3) * (arr snd - asMPFR 0.5) > 0))

-- firstRootBoundaryRight :: CPoint Real
-- firstRootBoundaryRight = firstRoot1 (arr snd < 0 || ((arr snd - asMPFR 0.5) * (arr snd - asMPFR 0.7) > 0))

-- -- Approaches 1 as is correct
-- firstRootAllNegative :: CPoint Real
-- firstRootAllNegative = firstRoot1 (arr snd < 0 || ((arr snd - asMPFR 10) < 0))

-- -- Approaches 0 as is correct
-- firstRootAllPositive :: CPoint Real
-- firstRootAllPositive = firstRoot1 (arr snd < 0 || ((arr snd - asMPFR 10) > 0))