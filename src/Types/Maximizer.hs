module Types.Maximizer where

import Prelude hiding (Real, (&&), (||), not, max, min, Ord (..), product, map, (^))
import FwdMode ((:~>), fstD, sndD, getDerivTower, (@.), VectorSpace)
import FwdPSh hiding (max, max01)
import Types.SmoothBool
import Types.OShape (OShape)
import Types.Real

type Maximizer a = (a :=> DReal) :=> DReal

point :: VectorSpace g => PShD a => a g -> Maximizer a g
point x = ArrD $ \wk f -> f # dmap wk x

compactUnion :: VectorSpace g => Maximizer a g -> (a :=> Maximizer b) g -> Maximizer b g
compactUnion i f = ArrD $ \wk p ->
  dmap wk i # (ArrD $ \wk' x -> (dmap (wk @. wk') f # x) # dmap wk' p)

product :: PShD a => VectorSpace g => Maximizer a g -> Maximizer b g -> Maximizer (a :* b) g
product ka kb = ArrD $ \wk p ->
  dmap wk          ka # (ArrD $ \wk' a ->
  dmap (wk @. wk') kb # (ArrD $ \wk'' b ->
    dmap (wk' @. wk'') p # (dmap wk'' a :* b)))

union :: VectorSpace g => Maximizer a g -> Maximizer a g -> Maximizer a g
union k k' = ArrD $ \wk p -> max (dmap wk k # p) (dmap wk k' # p)

map :: VectorSpace g => (a :=> b) g -> Maximizer a g -> Maximizer b g
map f k = ArrD $ \wk p -> dmap wk k # ArrD (\wk' x -> dmap wk' p # (dmap (wk @. wk') f # x))

sup :: VectorSpace g => Maximizer a g -> (a :=> DReal) g -> DReal g
sup k p = k # p

inf :: VectorSpace g =>  Maximizer a g -> (a :=> DReal) g -> DReal g
inf k p = - (k # ArrD (\wk x -> - (dmap wk p # x)))

infimum :: VectorSpace g => Maximizer DReal g -> DReal g
infimum k = inf k $ ArrD (\_ x -> x)

supremum :: VectorSpace g => Maximizer DReal g -> DReal g
supremum k = sup k $ ArrD (\_ x -> x)

hausdorffDist :: VectorSpace g => PShD a =>
  (a :* a :=> DReal) g -> Maximizer a g -> Maximizer a g -> DReal g
hausdorffDist d k k' =
  max (sup k  (ArrD (\wk x  -> inf (dmap wk k') (ArrD (\wk' x' -> dmap (wk @. wk') d # (dmap wk' x :* x'))))))
     (sup k' (ArrD (\wk x' -> inf (dmap wk k ) (ArrD (\wk' x  -> dmap (wk @. wk') d # (x :* dmap wk' x'))))))

separationDist :: VectorSpace g => PShD a =>
  (a :* a :=> DReal) g -> Maximizer a g -> Maximizer a g -> DReal g
separationDist d k k' =
  inf k' (ArrD (\wk x' -> inf (dmap wk k ) (ArrD (\wk' x  -> dmap (wk @. wk') d # (x :* dmap wk' x')))))

unit_interval :: VectorSpace g => Maximizer DReal g
unit_interval = ArrD $ \_ -> max01

unit_square :: VectorSpace g => Maximizer (DReal :* DReal) g
unit_square = product unit_interval unit_interval

quarter_disk :: VectorSpace g => Maximizer (DReal :* DReal) g
quarter_disk = quarter_disk_variable 1

quarter_disk_variable :: VectorSpace g => DReal g -> Maximizer (DReal :* DReal) g
quarter_disk_variable r = compactUnion unit_interval $ ArrD (\wk z ->
  compactUnion unit_interval $ ArrD (\wk' theta ->
  let r' = dmap (wk @. wk') r in
  let z' = dmap wk' z in
  point ((r' * z' * cos ((pi / 2) * theta)) :* (r' * z' * sin ((pi / 2) * theta)))))

d_R2 :: ((DReal :* DReal) :* (DReal :* DReal) :=> DReal) g
d_R2 = ArrD $ \_ ((x :* y) :* (x' :* y')) -> sqrt ((x - x')^2 + (y - y')^2)

d_R1 :: (DReal :* DReal :=> DReal) g
d_R1 = ArrD $ \_ (x :* x') -> (x - x')^2

circle :: VectorSpace g => DReal g -> Maximizer (DReal :* DReal) g
circle r = map (ArrD (\wk theta -> let r' = dmap wk r in
  (r' * cos (2 * pi * theta)) :* (r' * sin (2 * pi * theta)))) unit_interval

unit_square_perim :: VectorSpace g => Maximizer (DReal :* DReal) g
unit_square_perim = foldr1 union [ map f unit_interval | f <- fs ]
  where
  fs :: VectorSpace g => [(DReal :=> (DReal :* DReal)) g]
  fs = [ ArrD (\_ x -> (2 * x - 1) :* (-1))
       , ArrD (\_ x -> (2 * x - 1) :* 1)
       , ArrD (\_ y -> (-1) :* (2 * y - 1))
       , ArrD (\_ y -> 1 :* (2 * y - 1))]

exampleHausdorffDist :: DReal ()
exampleHausdorffDist = hausdorffDist d_R2 unit_square quarter_disk

exampleHausdorffDist2 :: DReal ()
exampleHausdorffDist2 = hausdorffDist d_R1 unit_interval unit_interval

-- Does this run?
exampleHausdorffDistDeriv :: DReal ()
exampleHausdorffDistDeriv = deriv (ArrD (\_ r -> hausdorffDist d_R2 unit_square (quarter_disk_variable r))) 1

xPlusY :: ((DReal :* DReal) :=> DReal) g
xPlusY = ArrD (\_ (x :* y) -> x + y)

exampleMaximization :: DReal ()
exampleMaximization = sup quarter_disk xPlusY

exampleMaximizationDeriv :: DReal ()
exampleMaximizationDeriv = deriv (ArrD (\_ r -> sup (quarter_disk_variable r) xPlusY)) 1

simplerMaximization :: DReal ()
simplerMaximization = supremum (map (ArrD (\_ x -> 0.5 * x)) unit_interval)

simpleDerivTest :: DReal ()
simpleDerivTest = deriv (ArrD (\_ c -> supremum ((map (ArrD (\wk x -> dmap wk c * x))) unit_interval))) 1.0