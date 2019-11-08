module SmoothLang where

import Prelude ()
import Expr
import RealExpr (runPoint, Point)
import MPFR (R)

sqrt2Example :: Point R
sqrt2Example = dedekind_cut (\x -> x < 0 || (x ^ 2) < 2)

quantificationExample :: Point Bool
quantificationExample = exists_unit_interval (\x -> isTrue (x < asMPFR 0.5 && x > 0.3))