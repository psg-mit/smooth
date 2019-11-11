{-# LANGUAGE TypeOperators #-}

module Types.SmoothBool where

import Prelude hiding (Real, (&&), (||), not, max, min, Ord (..))
import FwdMode ((:~>))
import FwdPSh
import MPFR (Real)

-- SBool = quotient of the reals by the smooth equivalence relation
-- x ~ y :=   x = y \/ (x < 0 /\ y < 0) \/ (x > 0 /\ y > 0)
newtype SBool g = SBool (DReal g)

true :: SBool g
true = SBool 1

false :: SBool g
false = SBool (-1)

not :: SBool g -> SBool g
not (SBool x) = SBool (- x)

(&&) :: SBool g -> SBool g -> SBool g
SBool (R x) && SBool (R y) = SBool (R (min x y))

(||) :: SBool g -> SBool g -> SBool g
SBool (R x) || SBool (R y) = SBool (R (max x y))

positive :: DReal g -> SBool g
positive = SBool

(<) :: DReal g -> DReal g -> SBool g
x < y = SBool (y - x)

(>) :: DReal g -> DReal g -> SBool g
x > y = SBool (x - y)

-- Currently, we have no nontrivial maps out of the smooth Booleans.
-- We should be able to have
-- dedekind_cut : (DReal => SBool) => DReal