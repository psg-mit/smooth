
module Types.SmoothBool where

import Prelude hiding (Real, (&&), (||), not, max, min, Ord (..))
import FwdMode ((:~>), fstD, sndD, getDerivTower)
import FwdPSh

-- SBool = quotient of the reals by the smooth equivalence relation
-- x ~ y :=   x = y \/ (x < 0 /\ y < 0) \/ (x > 0 /\ y > 0)
newtype SBool g = SBool (DReal g)

true :: SBool g
true = SBool 1

false :: SBool g
false = SBool (-1)

not :: SBool g -> SBool g
not (SBool x) = SBool (- x)

infix 3 &&
(&&) :: SBool g -> SBool g -> SBool g
SBool (R x) && SBool (R y) = SBool (R (min x y))

infix 2 ||
(||) :: SBool g -> SBool g -> SBool g
SBool (R x) || SBool (R y) = SBool (R (max x y))

positive :: DReal g -> SBool g
positive = SBool

infix 4 <
(<) :: DReal g -> DReal g -> SBool g
x < y = SBool (y - x)

infix 4 >
(>) :: DReal g -> DReal g -> SBool g
x > y = SBool (x - y)

-- Currently, we have no nontrivial maps out of the smooth Booleans.
-- We should be able to have
-- dedekind_cut : (DReal => SBool) => DReal

dedekind_cut :: Additive g => (ArrD DReal SBool) g -> DReal g
dedekind_cut (ArrD f) = R (FwdPSh.newton_cut' (let SBool (R b) = f fstD (R sndD) in b))

testBSqrt :: Point Real -> [Point Real]
testBSqrt c = let R z = dedekind_cut (ArrD (\c x -> x < 0 || x^2 < R c)) in
    getDerivTower z c