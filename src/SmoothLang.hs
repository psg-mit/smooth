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
firstRootp5 :: CPoint RootResult
firstRootp5 = firstRoot1 (arr snd < 0.5)

-- Undetermined to 0
firstRootpg5 :: CPoint RootResult
firstRootpg5 = firstRoot1 (arr snd > 0.5)

-- Root 0.5
firstRootInTheMiddle :: CPoint RootResult
firstRootInTheMiddle = firstRoot1 (arr snd < 0 || (arr snd ^ 2) < 1/4)

-- Should go to zero?
firstRootOfDoublePM :: CPoint RootResult
firstRootOfDoublePM = firstRoot1 (arr snd < 0 || ((arr snd - asMPFR 0.3) * (arr snd - asMPFR 0.7) < 0))

-- Should go to 0.3
firstRootOfDoubleMP :: CPoint RootResult
firstRootOfDoubleMP = firstRoot1 (arr snd < 0 || ((arr snd - asMPFR 0.3) * (arr snd - asMPFR 0.7) > 0))

firstRootBoundaryLeft :: CPoint RootResult
firstRootBoundaryLeft = firstRoot1 (arr snd < 0 || ((arr snd - asMPFR 0.3) * (arr snd - asMPFR 0.5) > 0))

firstRootBoundaryRight :: CPoint RootResult
firstRootBoundaryRight = firstRoot1 (arr snd < 0 || ((arr snd - asMPFR 0.5) * (arr snd - asMPFR 0.7) > 0))

-- NoRoot
firstRootAllNegative :: CPoint RootResult
firstRootAllNegative = firstRoot1 ((arr snd - asMPFR 10) < 0)

-- NoRoot
firstRootAllPositive :: CPoint RootResult
firstRootAllPositive = firstRoot1 ((arr snd - asMPFR 10) > 0)

-- Approaches 0 as is correct
-- but frozen at [0,1] is also okay
firstRootToZero :: CPoint RootResult
firstRootToZero = firstRoot1 (arr snd < 0 || ((arr snd) > 0))

-- Approaches 0 as is correct
firstRootToOne :: CPoint RootResult
firstRootToOne = firstRoot1 (arr snd < 0 || ((arr snd - asMPFR 1) < 0))