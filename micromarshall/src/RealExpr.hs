{-# LANGUAGE TypeFamilies, ExistentialQuantification #-}

module RealExpr where

import Data.Number.MPFR hiding (Precision)
import Data.IORef

import Interval
import Rounded (Rounded, Prec, RoundDir (Up, Down))

class Approx a where
  data Compact a :: *
  constant :: a -> Compact a
  bottom :: Compact a

instance Approx MPFR where
  data Compact MPFR = CompactMPFR (Interval MPFR)
  constant x = CompactMPFR (lift x)
  bottom = CompactMPFR realLine

instance Approx () where
  data Compact () = CompactUnit
  constant () = CompactUnit
  bottom = CompactUnit

instance (Approx a, Approx b) => Approx (a, b) where
  data Compact (a, b) = CompactPair (Compact a) (Compact b)
  constant (x, y) = CompactPair (constant x) (constant y)
  bottom = CompactPair bottom bottom

class Precision p where
  initPrecision :: p
  nextPrecision :: p -> p

instance Precision () where
  initPrecision = ()
  nextPrecision _ = ()

instance Precision Word where
  initPrecision = 1
  nextPrecision n = n + 1

instance (Precision a, Precision b) => Precision (a, b) where
  initPrecision = (initPrecision, initPrecision)
  nextPrecision (p, p') = (nextPrecision p, nextPrecision p')

data RFunc a b = forall p. Precision p =>  RFunc
  { func :: Compact a -> p -> Compact b
  , currApprox :: Compact b
  , currPrec :: p
  }

data RealExpr a =
    Constant a
  | Plus (RealExpr a) (RealExpr a)
  | Mul (RealExpr a) (RealExpr a)

rfuncI :: Precision p => (Compact a -> p -> Compact b) -> Compact b -> RFunc a b
rfuncI f a = RFunc f a initPrecision

econst :: Approx a => a -> RFunc g a
econst x = rfuncI (\_ () -> constant x) (constant x)

eRealOp2 :: (Prec -> Interval MPFR -> Interval MPFR -> Interval MPFR) -> RFunc (MPFR, MPFR) MPFR
eRealOp2 op = rfuncI (\(CompactPair (CompactMPFR ix) (CompactMPFR iy)) p -> CompactMPFR (op p ix iy)) (CompactMPFR realLine)

eplus :: RFunc (MPFR, MPFR) MPFR
eplus = eRealOp2 iadd

emul :: RFunc (MPFR, MPFR) MPFR
emul = eRealOp2 imul

ecompose :: RFunc a b -> RFunc b c -> RFunc a c
ecompose (RFunc f1 a1 p1) (RFunc f2 a2 p2) =
  RFunc (\i (p1, p2) -> f2 (f1 i p1) p2) a2 (p1, p2)

eprod :: RFunc g a -> RFunc g b -> RFunc g (a, b)
eprod (RFunc f1 a1 p1) (RFunc f2 a2 p2) =
  RFunc (\i (p1, p2) -> CompactPair (f1 i p1) (f2 i p2)) (CompactPair a1 a2) (p1, p2)

emapOut :: (Compact a -> Compact b) -> RFunc g a -> RFunc g b
emapOut f (RFunc aprx a p) = RFunc (\i p -> f (aprx i p)) (f a) p

emap :: Approx b => (Compact a -> Compact b) -> RFunc a b
emap f = RFunc (\i _ -> f i) bottom ()

efst :: Approx a => RFunc (a, b) a
efst = emap (\(CompactPair a b) -> a)

esnd :: Approx b => RFunc (a, b) b
esnd = emap (\(CompactPair a b) -> b)

eid :: Approx a => RFunc a a
eid = RFunc (\i _ -> i) bottom ()

edup  :: Approx a => RFunc a (a, a)
edup = RFunc (\i _ -> CompactPair i i) bottom ()

runRFunc :: Approx a => RFunc () a -> [Compact a]
runRFunc (RFunc f a p) = let p' = nextPrecision p in
  a : runRFunc (RFunc f (f CompactUnit p') p')

econstD :: Double -> RFunc g MPFR
econstD i = econst (fromDouble Data.Number.MPFR.Down 10 i)

test :: [(MPFR, MPFR)]
test = runRFuncMPFR (ap2 eplus (econstD 1.3) (econstD 2))

runRFuncMPFR :: RFunc () MPFR -> [(MPFR, MPFR)]
runRFuncMPFR = fmap f . runRFunc
  where
  f (CompactMPFR (Interval a b)) = (a, b)

ap2 :: RFunc (a, b) c -> RFunc g a -> RFunc g b -> RFunc g c
ap2 f x y = eprod x y `ecompose` f