module SmoothLang where

import Prelude ()
import Control.Arrow ((&&&))
import Expr
import RealExpr (runPoint, Point)
import qualified RealExpr as RE
import MPFR (Real)

sqrt2Example :: Point Real
sqrt2Example = dedekind_cut (\x -> x < 0 || (x ^ 2) < 2)

quantificationExample :: Point Bool
quantificationExample = exists_unit_interval (\x -> isTrue (x < asMPFR 0.5 && x > 0.3))

newtonSqrt2Example :: Point Real
newtonSqrt2Example = newton_cut (\x -> max (-x) (2 - x^2) &&& ap1 RE.max_deriv ((-x &&& (2 - x^2)) &&& (-1 &&& -2*x)))