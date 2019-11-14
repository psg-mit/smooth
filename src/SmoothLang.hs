module SmoothLang where

import Prelude ()
import Expr
import RealExpr (runCMap, firstRoot)
import MPFR (R, showReal)

sqrt2Example :: CMap () R
sqrt2Example = dedekind_cut (\x -> x < 0 || (x ^ 2) < 2)

quantificationExample :: CMap () Bool
quantificationExample = exists_unit_interval (\x -> isTrue (x < asMPFR 0.5 && x > 0.3))

firstRootExample :: CMap () Bool
firstRootExample = firstRoot (\x -> (x ^ 2) < 2)
