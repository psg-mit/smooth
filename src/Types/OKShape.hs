module Types.OKShape where

import Prelude hiding (Real, (&&), (||), not, max, min, Ord (..), product, map)
import FwdMode ((@.), VectorSpace)
import FwdPSh ((:*) (..), Additive, PShD, (:=>) (..), dmap, (#))
import Types.SmoothBool
import Types.OShape (OShape)
import Types.KShape (KShape)
import qualified Types.OShape as O
import qualified Types.KShape as K

type OKShape a = KShape a :* OShape a

empty :: OKShape a g
empty = K.empty :* O.empty

union :: VectorSpace g => OKShape a g -> OKShape a g -> OKShape a g
union (k :* o) (k' :* o') = K.union k k' :* O.union o o'


compactUnionO :: PShD f => VectorSpace g => KShape e g -> (e :=> OShape f) g -> OShape f g
compactUnionO k o = ArrD $ \wk f -> K.exists (dmap wk k) (ArrD (\wk' e -> dmap (wk @. wk') o # e # dmap wk' f))

compactIntersectionO :: PShD f => VectorSpace g => KShape e g -> (e :=> OShape f) g -> OShape f g
compactIntersectionO k o = ArrD $ \wk f -> K.forall (dmap wk k) (ArrD (\wk' e -> dmap (wk @. wk') o # e # dmap wk' f))