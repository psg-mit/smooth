module Types.KShape where

import Prelude hiding (Real, (&&), (||), not, max, min, Ord (..), product, map, (^))
import FwdMode ((:~>), fstD, sndD, getDerivTower, (@.), VectorSpace)
import FwdPSh hiding (max)
import Types.SmoothBool
import Types.OShape (OShape)
import Types.Real
import qualified Types.OShape as O

type KShape a = (a :=> SBool) :=> SBool
-- type Maximizer a = (a :=> DReal) :=> DReal

point :: VectorSpace g => PShD a => a g -> KShape a g
point x = ArrD $ \wk f -> f # dmap wk x

compactUnion :: VectorSpace g => KShape a g -> (a :=> KShape b) g -> KShape b g
compactUnion i f = ArrD $ \wk p ->
  dmap wk i # (ArrD $ \wk' x -> (dmap (wk @. wk') f # x) # dmap wk' p)

product :: PShD a => VectorSpace g => KShape a g -> KShape b g -> KShape (a :* b) g
product ka kb = ArrD $ \wk p ->
  dmap wk          ka # (ArrD $ \wk' a ->
  dmap (wk @. wk') kb # (ArrD $ \wk'' b ->
    dmap (wk' @. wk'') p # (dmap wk'' a :* b)))


empty :: KShape a g
empty = ArrD $ \_ p -> true

union :: VectorSpace g => KShape a g -> KShape a g -> KShape a g
union k k' = ArrD $ \wk p -> dmap wk k # p && dmap wk k' # p

intersect :: VectorSpace g => KShape a g -> OShape a g -> KShape a g
intersect k o = ArrD $ \wk p ->
  dmap wk k # (ArrD $ \wk' x -> not (dmap (wk @. wk') o # x) || dmap wk' p # x)

difference :: VectorSpace g => KShape a g -> OShape a g -> KShape a g
difference k o = intersect k (O.complement o)

map :: VectorSpace g => (a :=> b) g -> KShape a g -> KShape b g
map f k = ArrD $ \wk p -> dmap wk k # ArrD (\wk' x -> dmap wk' p # (dmap (wk @. wk') f # x))

forall :: VectorSpace g => KShape a g -> (a :=> SBool) g -> SBool g
forall k p = k # p

exists :: VectorSpace g =>  KShape a g -> (a :=> SBool) g -> SBool g
exists k p = not (k # ArrD (\wk x -> not (dmap wk p # x)))

isEmpty :: VectorSpace g => KShape a g -> SBool g
isEmpty k = k # ArrD (\_ _ -> false)

infimum :: VectorSpace g => KShape DReal g -> DReal g
infimum k = dedekind_cut $ ArrD (\wk q -> forall (dmap wk k) (ArrD (\wk' x -> dmap wk' q < x)))

supremum :: VectorSpace g => KShape DReal g -> DReal g
supremum k = dedekind_cut $ ArrD (\wk q -> exists (dmap wk k) (ArrD (\wk' x -> dmap wk' q < x)))

inf :: VectorSpace g => KShape a g -> (a :=> DReal) g -> DReal g
inf k f = infimum (map f k)

sup :: VectorSpace g => KShape a g -> (a :=> DReal) g -> DReal g
sup k f = supremum (map f k)

hausdorffDist :: VectorSpace g => PShD a =>
  (a :* a :=> DReal) g -> KShape a g -> KShape a g -> DReal g
hausdorffDist d k k' =
  max (sup k  (ArrD (\wk x  -> inf (dmap wk k') (ArrD (\wk' x' -> dmap (wk @. wk') d # (dmap wk' x :* x'))))))
      (sup k' (ArrD (\wk x' -> inf (dmap wk k ) (ArrD (\wk' x  -> dmap (wk @. wk') d # (x :* dmap wk' x'))))))

separationDist :: VectorSpace g => PShD a =>
  (a :* a :=> DReal) g -> KShape a g -> KShape a g -> DReal g
separationDist d k k' =
  inf k' (ArrD (\wk x' -> inf (dmap wk k ) (ArrD (\wk' x  -> dmap (wk @. wk') d # (x :* dmap wk' x')))))

unit_interval :: VectorSpace g => KShape DReal g
unit_interval = ArrD $ \_ -> forall01

unit_square :: VectorSpace g => KShape (DReal :* DReal) g
unit_square = product unit_interval unit_interval

quarter_disk :: VectorSpace g => KShape (DReal :* DReal) g
quarter_disk = intersect unit_square O.unitDisk

quarter_disk_variable :: VectorSpace g => DReal g -> KShape (DReal :* DReal) g
quarter_disk_variable r = intersect unit_square $
  ArrD $ \wk (x :* y) -> x^2 + y^2 < (dmap wk r)^2

d_R2 :: ((DReal :* DReal) :* (DReal :* DReal) :=> DReal) g
d_R2 = ArrD $ \_ ((x :* y) :* (x' :* y')) -> (x - x')^2 + (y - y')^2

d_R1 :: (DReal :* DReal :=> DReal) g
d_R1 = ArrD $ \_ (x :* x') -> (x - x')^2

exampleHausdorffDist :: DReal ()
exampleHausdorffDist = hausdorffDist d_R2 unit_square quarter_disk

-- Seems to be converging, but slowly. Derivatives
-- must not be working, because it's only progressing through bisection.
exampleHausdorffDist2 :: DReal ()
exampleHausdorffDist2 = hausdorffDist d_R1 unit_interval unit_interval

xPlusY :: ((DReal :* DReal) :=> DReal) g
xPlusY = ArrD (\_ (x :* y) -> x + y)

exampleMaximization :: DReal ()
exampleMaximization = sup quarter_disk xPlusY

-- Doesn't seem to converge at the moment
exampleMaximizationDeriv :: DReal ()
exampleMaximizationDeriv = deriv (ArrD (\_ r -> sup (quarter_disk_variable r) xPlusY)) 1

simplerMaximization :: DReal ()
simplerMaximization = supremum (intersect unit_interval (ArrD $ \wk x -> x < 0.5))

-- Still not converging, but it should
simplerMaximizationDeriv :: DReal ()
simplerMaximizationDeriv = deriv (ArrD (\_ r -> supremum (intersect unit_interval (ArrD $ \wk x -> x < dmap wk r)))) 0.5

simpleDerivTest :: DReal ()
simpleDerivTest = deriv (ArrD (\_ c -> supremum ((map (ArrD (\wk x -> dmap wk c * x))) unit_interval))) 1.0