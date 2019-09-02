{-# LANGUAGE TypeFamilies, ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving, DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE Arrows #-}

module RealExpr where

import Control.Category hiding ((.), id)
import qualified Control.Category as C
import Control.Arrow
import Data.Number.MPFR hiding (Precision)
import Data.IORef
import Debug.Trace

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

instance Category RFunc where
  id = arr id
  (.) = flip ecompose

instance Arrow RFunc where
  arr f = RFunc $ \x -> (f x, arr f)
  RFunc f *** RFunc g = RFunc $ \(x, y) ->
    let (a, f') = f x in let (b, g') = g y in
    ((a, b), f' *** g')

withPrec :: (Prec -> a -> b) -> RFunc a b
withPrec f = withPrec' 1 where
  withPrec' p = RFunc $ \x -> (f p x, withPrec' (p + 1))

withPrec2 :: (Prec -> a -> b -> c) -> RFunc (a, b) c
withPrec2 op = withPrec $ \p (ix, iy) -> op p ix iy


econst :: a -> RFunc g a
econst x = arr (const x)

eplus :: Rounded a => RFunc (Interval a, Interval a) (Interval a)
eplus = withPrec2 iadd

emul :: Rounded a => RFunc (Interval a, Interval a) (Interval a)
emul = withPrec2 imul

epow :: Rounded a => Int -> RFunc (Interval a) (Interval a)
epow k = withPrec (\p x -> Interval.pow p x k)

emax :: Rounded a => RFunc (Interval a, Interval a) (Interval a)
emax = withPrec2 (\p -> imax)

enegate :: Rounded a => RFunc (Interval a) (Interval a)
enegate = withPrec inegate

esqrt' :: Rounded a => Interval a -> Prec -> RFunc (Interval a) (Interval a)
esqrt' i p = RFunc $ \x ->
  let i' = maybe_cut_bisection (\q -> let q' = lift q in icmp (Interval.pow p q' 2) x) i
  in (i', esqrt' i' (p + 1))

esqrt :: Rounded a => RFunc (Interval a) (Interval a)
esqrt = RFunc $ \i -> let ir = irecip 1 i in let i' = iunion i ir in
  (i', esqrt' i' 1)

type B = (Bool, Bool)

-- Not sure that this is right with the increasing precision in gab'
secondOrderPrim :: RFunc (a -> b) c -> RFunc (g, a) b -> RFunc g c
secondOrderPrim (RFunc abc) (RFunc gab) = RFunc $ \g ->
    let (c, abc') = abc (\a -> let (b, gab') = gab (g, a) in b) in
    let (_, gab') = gab (g, undefined) in
    (c, secondOrderPrim abc' gab')

elt :: Rounded a => RFunc (Interval a, Interval a) B
elt = arr (\(Interval l1 u1, Interval l2 u2) -> (u1 < l2, l1 > u2))

eand :: RFunc (B, B) B
eand = arr (\((t1, f1), (t2, f2)) -> (t1 && t2, f1 || f2))

eor :: RFunc (B, B) B
eor = arr (\((t1, f1), (t2, f2)) -> (t1 || t2, f1 && f2))

eneg :: RFunc B B
eneg = arr (\(x, y) -> (y, x))

integral' :: (Show a, Rounded a) => Prec -> Interval a -> RFunc (Interval a -> Interval a) (Interval a)
integral' p i@(Interval a b) = RFunc $ \f ->
  let m = R.average a b in
  -- traceShow p $
  (imul p (Interval.isub p (lift b) (lift a)) (f i), proc f' -> do
     x1 <- integral' (p + 20) (Interval a m) -< f'
     x2 <- integral' (p + 20) (Interval m b) -< f'
     returnA -< iadd (p + 20) x1 x2)

forall_interval' :: (Show a, Rounded a) => Prec -> Interval a -> RFunc (Interval a -> Bool) Bool
forall_interval' p i@(Interval a b) = RFunc $ \f ->
  let m = R.average a b in
  -- traceShow p $
  (f i, proc f' -> do
    t1 <- forall_interval' (p + 20) (Interval a m) -< f'
    t2 <- forall_interval' (p + 20) (Interval m b) -< f'
    returnA -< t1 && t2)

exists_interval' :: (Show a, Rounded a) => Prec -> Interval a -> RFunc (Interval a -> Bool) Bool
exists_interval' p i@(Interval a b) = RFunc $ \f ->
  let m = R.average a b in
  -- traceShow p $
  (f (lift m), proc f' -> do
    t1 <- exists_interval' (p + 20) (Interval a m) -< f'
    t2 <- exists_interval' (p + 20) (Interval m b) -< f'
    returnA -< t1 || t2)

dedekind_cut' :: Rounded a => RFunc (Interval a -> B) (Interval a)
dedekind_cut' = bound 1 R.one where
  bound p b = RFunc $ \f -> let negb = R.neg p R.Down b in
    if fst (f (lift negb)) && snd (f (lift b))
      then let i = Interval negb b in (i, locate p i)
      else (realLine, bound (p + 1) (R.double p R.Down b))
  locate p (Interval l u) = RFunc $ \f ->
    let (l', u') = (let m = R.average l u in
                        case f (lift m) of
                          (True, _) -> (m, u)
                          (_, True) -> (l, m)
                          _ -> let mu = R.average m u in
                            case f (lift mu) of
                              (True, _) -> (mu, u)
                              (_, True) -> (l, mu)
                              _ -> (l, u))
    in let i' = Interval l' u' in (i', locate p i')

-- class Extends g d where
--   proj :: RFunc d g

-- instance Extends g g where
--   proj = eid

-- instance Extends g d => Extends g (d, a) where
--   proj = ecompose efst proj


ecompose :: RFunc a b -> RFunc b c -> RFunc a c
ecompose (RFunc f1) (RFunc f2) =
  RFunc (\a -> let (b, f1') = f1 a in let (c, f2') = f2 b in (c, ecompose f1' f2'))

eprod :: RFunc g a -> RFunc g b -> RFunc g (a, b)
eprod (RFunc f1) (RFunc f2) =
  RFunc (\i -> let (a, f1') = f1 i in let (b, f2') = f2 i in ((a, b), eprod f1' f2'))

runRFunc :: RFunc () a -> [a]
runRFunc (RFunc f) = let (x, f') = f () in
  x : runRFunc f'

econstD :: Rounded r => Double -> RFunc g (Interval r)
econstD i = econst (lift (R.fromDouble 52 R.Down i))

constMPFR :: Double -> RFunc g (Interval MPFR)
constMPFR = econstD

runRFuncMPFR :: RFunc () R -> [(MPFR, MPFR)]
runRFuncMPFR = fmap f . runRFunc
  where
  f (Interval a b) = (a, b)

ap2 :: RFunc (a, b) c -> RFunc g a -> RFunc g b -> RFunc g c
ap2 f x y = f <<< eprod x y

ap1 :: RFunc a b -> RFunc g a -> RFunc g b
ap1 f = (f <<<)

abs1 :: (forall d. RFunc d g -> RFunc d a -> RFunc d b) -> RFunc (g, a) b
abs1 f = f (arr fst) (arr snd)