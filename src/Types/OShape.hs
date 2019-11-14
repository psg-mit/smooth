module Types.OShape where

import Prelude hiding (Real, (&&), (||), not, max, min, Ord (..), product)
import FwdMode ((:~>), fstD, sndD, getDerivTower)
import FwdPSh
import Types.SmoothBool

type OShape a = a :=> SBool

unitInterval :: OShape DReal g
unitInterval = ArrD $ \_ x -> 0 < x && x < 1

unitDisk :: OShape (DReal :* DReal) g
unitDisk = ArrD $ \_ (x :* y) -> x^2 + y^2 < 1

rectangle :: Additive g => DReal g -> DReal g -> OShape (DReal :* DReal) g
rectangle width height = ArrD $ \wk (x :* y) ->
     (- dmap wk  width / 2) < x && x < (dmap wk  width / 2)
  && (- dmap wk height / 2) < y && y < (dmap wk height / 2)

unitSquare :: Additive g => OShape (DReal :* DReal) g
unitSquare = rectangle 2 2

product :: Additive g => OShape a g -> OShape b g -> OShape (a :* b) g
product fa fb = ArrD $ \wk (x :* y) -> dmap wk fa # x && dmap wk fb # y

empty :: OShape a g
empty = ArrD $ \_ _ -> false

full :: OShape a g
full = ArrD $ \_ _ -> true

union :: Additive g => OShape a g -> OShape a g -> OShape a g
union o o' = ArrD $ \wk x -> dmap wk o # x || dmap wk o' # x

intersection :: Additive g => OShape a g -> OShape a g -> OShape a g
intersection o o' = ArrD $ \wk x -> dmap wk o # x && dmap wk o' # x

complement :: Additive g => OShape a g -> OShape a g
complement o = ArrD $ \wk x -> dmap wk o # x

isIn :: Additive g => a g -> OShape a g -> SBool g
isIn x o = o # x

contramap :: Additive g => (b :=> a) g -> OShape a g -> OShape b g
contramap f o = ArrD $ \wk x -> dmap wk o # (dmap wk f # x)