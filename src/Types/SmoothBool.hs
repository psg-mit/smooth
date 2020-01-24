{-# LANGUAGE FlexibleInstances #-}

module Types.SmoothBool where

import qualified Prelude
import Prelude hiding (Real, (&&), (||), not, max, min, Ord (..))
import FwdMode ((:~>), fstD, sndD, getDerivTower, getValue)
import FwdPSh
import Interval (Interval (..))
import Data.List (intercalate)
import RealExpr (runPoint)
import qualified Rounded as R

-- SBool = quotient of the reals by the smooth equivalence relation
-- x ~ y :=   x = y \/ (x < 0 /\ y < 0) \/ (x > 0 /\ y > 0)
newtype SBool g = SBool (DReal g)

instance Show (SBool ()) where
  show (SBool (R x)) = go . runPoint $ getValue x where
    go (Interval a b : xs)
      | a Prelude.> R.zero = "true"
      | b Prelude.< R.zero = "false"
      | otherwise = "?\n" ++ go xs

true :: SBool g
true = SBool 1

false :: SBool g
false = SBool (-1)

not :: SBool g -> SBool g
not (SBool x) = SBool (- x)

infixr 3 &&
(&&) :: SBool g -> SBool g -> SBool g
SBool (R x) && SBool (R y) = SBool (R (min x y))

infixr 2 ||
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

-- Describe a real number by a predicate saying what it means
-- to be less than it.
-- x < dedekind_cut P  iff P x
dedekind_cut :: Additive g => (DReal :=> SBool) g -> DReal g
dedekind_cut (ArrD f) = R (FwdPSh.newton_cut' (let SBool (R b) = f fstD (R sndD) in b))

forall01 :: Additive g => (DReal :=> SBool) g -> SBool g
forall01 (ArrD f) = positive (R (FwdPSh.min01' (let SBool (R b) = f fstD (R sndD) in b)))

exists01 :: Additive g => (DReal :=> SBool) g -> SBool g
exists01 (ArrD f) = positive (R (FwdPSh.max01' (let SBool (R b) = f fstD (R sndD) in b)))

dedekind_cubert :: Additive g => DReal g -> DReal g
dedekind_cubert z = dedekind_cut (ArrD (\wk x -> x < 0 || x^3 < dmap wk z))

testBSqrt :: CPoint Real -> [CPoint Real]
testBSqrt z = let R f = dedekind_cut (ArrD (\c x -> x < 0 || x^2 < R c)) in
    getDerivTower f z