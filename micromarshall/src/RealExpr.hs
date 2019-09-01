{-# LANGUAGE TypeFamilies, ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving, DeriveFunctor #-}

module RealExpr where

import Data.Number.MPFR hiding (Precision)
import Data.IORef

import Interval
import Rounded (Rounded, Prec, RoundDir (Up, Down))
import qualified Rounded as R

type R = Interval MPFR

class HasBottom a where
  bottom :: a

instance Rounded a => HasBottom (Interval a) where
  bottom = Interval R.negativeInfinity R.positiveInfinity

instance HasBottom () where
  bottom = ()

instance (HasBottom a, HasBottom b) => HasBottom (a, b) where
  bottom = (bottom, bottom)

data RFunc a b = RFunc (a -> (b, RFunc a b))

deriving instance Functor (RFunc a)

emap :: (a -> b) -> RFunc a b
emap f = RFunc $ \x -> (f x, emap f)

withPrec :: (Prec -> a -> b) -> RFunc a b
withPrec f = withPrec' 1 where
  withPrec' p = RFunc $ \x -> (f p x, withPrec' (p + 1))

econst :: a -> RFunc g a
econst x = emap (const x)

eRealOp2 :: (Prec -> a -> a -> a) -> RFunc (a, a) a
eRealOp2 op = withPrec $ \p (ix, iy) -> op p ix iy

eplus :: Rounded a => RFunc (Interval a, Interval a) (Interval a)
eplus = eRealOp2 iadd

emul :: Rounded a => RFunc (Interval a, Interval a) (Interval a)
emul = eRealOp2 imul

emax :: Rounded a => RFunc (Interval a, Interval a) (Interval a)
emax = eRealOp2 (\p -> imax)

enegate :: Rounded a => RFunc (Interval a) (Interval a)
enegate = withPrec inegate

esqrt' :: Rounded a => Interval a -> Prec -> RFunc (Interval a) (Interval a)
esqrt' i p = RFunc $ \x ->
  let i' = maybe_cut_bisection (\q -> let q' = lift q in icmp (Interval.pow p q' 2) x) i
  in (i', esqrt' i' (p + 1))

esqrt :: Rounded a => RFunc (Interval a) (Interval a)
esqrt = RFunc $ \i -> let ir = irecip 1 i in let i' = iunion i ir in
  (i', esqrt' i' 1)

ecompose :: RFunc a b -> RFunc b c -> RFunc a c
ecompose (RFunc f1) (RFunc f2) =
  RFunc (\a -> let (b, f1') = f1 a in let (c, f2') = f2 b in (c, ecompose f1' f2'))

eprod :: RFunc g a -> RFunc g b -> RFunc g (a, b)
eprod (RFunc f1) (RFunc f2) =
  RFunc (\i -> let (a, f1') = f1 i in let (b, f2') = f2 i in ((a, b), eprod f1' f2'))

efst :: RFunc (a, b) a
efst = emap fst

esnd :: RFunc (a, b) b
esnd = emap snd

eid :: RFunc a a
eid = emap id

edup  :: RFunc a (a, a)
edup = emap (\i -> (i,i))

runRFunc :: RFunc () a -> [a]
runRFunc (RFunc f) = let (x, f') = f () in
  x : runRFunc f'

econstD :: Rounded r => Double -> RFunc g (Interval r)
econstD i = econst (lift (R.fromDouble 52 R.Down i))

test :: [(MPFR, MPFR)]
test = runRFuncMPFR (ap2 eplus (econstD 1.3) (econstD 2))

runRFuncMPFR :: RFunc () R -> [(MPFR, MPFR)]
runRFuncMPFR = fmap f . runRFunc
  where
  f (Interval a b) = (a, b)

ap2 :: RFunc (a, b) c -> RFunc g a -> RFunc g b -> RFunc g c
ap2 f x y = eprod x y `ecompose` f

ap1 :: RFunc a b -> RFunc g a -> RFunc g b
ap1 f = (`ecompose` f)

abs1 :: (forall d. RFunc d g -> RFunc d a -> RFunc d b) -> RFunc (g, a) b
abs1 f = f efst esnd