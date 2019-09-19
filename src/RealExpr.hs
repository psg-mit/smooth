{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving, DeriveFunctor #-}
{-# LANGUAGE Arrows #-}

module RealExpr where

import Prelude
import Control.Category hiding ((.), id)
import qualified Control.Category as C
import Control.Arrow
import Data.Number.MPFR (MPFR)
import Data.IORef
import Data.Ratio (numerator, denominator)
import Debug.Trace

import Interval (Interval (..))
import qualified Interval as I
import Rounded (Rounded, Prec, RoundDir (Up, Down))
import qualified Rounded as R

data CMap a b = CMap (a -> (b, CMap a b))
deriving instance Functor (CMap a)

instance Category CMap where
  id = arr id
  CMap g . CMap f = CMap $ \a ->
    let (b, f') = f a in let (c, g') = g b in (c, g' C.. f')

instance Arrow CMap where
  arr f = CMap $ \x -> (f x, arr f)
  CMap f *** CMap g = CMap $ \(x, y) ->
    let (a, f') = f x in let (b, g') = g y in
    ((a, b), f' *** g')
  CMap f1 &&& CMap f2 = CMap $ \i ->
    let (a, f1') = f1 i in let (b, f2') = f2 i in ((a, b), f1' &&& f2')

-- Not sure that this is right with the increasing precision in gab'
secondOrderPrim :: CMap (a -> b) c -> CMap (g, a) b -> CMap g c
secondOrderPrim (CMap abc) (CMap gab) = CMap $ \g ->
    let (c, abc') = abc (\a -> let (b, gab') = gab (g, a) in b) in
    let (_, gab') = gab (g, undefined) in
    (c, secondOrderPrim abc' gab')

withPrec :: (Prec -> a -> b) -> CMap a b
withPrec f = withPrec' 32 where
  withPrec' p = CMap $ \x -> (f p x, withPrec' (p + 1))

withPrec2 :: (Prec -> a -> b -> c) -> CMap (a, b) c
withPrec2 op = withPrec $ \p (ix, iy) -> op p ix iy

add :: Rounded a => CMap (Interval a, Interval a) (Interval a)
add = withPrec2 I.add

mul :: Rounded a => CMap (Interval a, Interval a) (Interval a)
mul = withPrec2 I.mul

recip :: Rounded a => CMap (Interval a) (Interval a)
recip = withPrec I.recip

div :: Rounded a => CMap (Interval a, Interval a) (Interval a)
div = proc (x, y) -> do
  ry <- RealExpr.recip -< y
  mul -< (x, ry)

pow :: Rounded a => Int -> CMap (Interval a) (Interval a)
pow k = withPrec (\p x -> I.pow p x k)

max :: Rounded a => CMap (Interval a, Interval a) (Interval a)
max = withPrec2 (\p -> I.max)

negate :: Rounded a => CMap (Interval a) (Interval a)
negate = withPrec I.negate

sqrtWithBisection' :: Rounded a => Interval a -> Prec -> CMap (Interval a) (Interval a)
sqrtWithBisection' i p = CMap $ \x ->
  let i' = I.maybe_cut_bisection (\q -> let q' = I.lift q in I.cmp (I.pow p q' 2) x) i
  in (i', sqrtWithBisection' i' (p + 1))

sqrtWithBisection :: Rounded a => CMap (Interval a) (Interval a)
sqrtWithBisection = CMap $ \i -> let ir = I.recip 1 i in let i' = I.union i ir in
  (i', sqrtWithBisection' i' 32)

join :: Rounded a => CMap (Interval a, Interval a) (Interval a)
join = arr (uncurry I.join)

lower :: Rounded a => CMap (Interval a) (Interval a)
lower = arr (\(Interval l u) -> Interval l R.positiveInfinity)

upper :: Rounded a => CMap (Interval a) (Interval a)
upper = arr (\(Interval l u) -> Interval R.negativeInfinity u)

mkInterval ::  CMap (Interval a, Interval a) (Interval a)
mkInterval = arr (\(Interval l1 u1, Interval l2 u2) -> Interval l1 u2)

signum :: Rounded a => CMap (Interval a) (Interval a)
signum = arr $ \(Interval l u) ->
  if l > R.zero
    then I.lift R.one
    else if u < R.zero
    then I.lift R.negativeOne
    else Interval R.negativeOne R.one

signum_deriv :: Rounded a => CMap (Interval a) (Interval a)
signum_deriv = arr $ \(Interval l u) ->
  if l > R.zero || u < R.zero
    then I.lift R.zero
    else I.realLine

type B = (Bool, Bool)

lt :: Rounded a => CMap (Interval a, Interval a) B
lt = arr (\(Interval l1 u1, Interval l2 u2) -> (u1 < l2, l1 > u2))

and :: CMap (B, B) B
and = arr (\((t1, f1), (t2, f2)) -> (t1 && t2, f1 || f2))

or :: CMap (B, B) B
or = arr (\((t1, f1), (t2, f2)) -> (t1 || t2, f1 && f2))

neg :: CMap B B
neg = arr (\(x, y) -> (y, x))

integral' :: Rounded a => Prec -> Interval a -> CMap (Interval a -> Interval a) (Interval a)
integral' p i@(Interval a b) = CMap $ \f ->
  let m = R.average a b in
  -- traceShow p $
  (I.mul p (I.sub p (I.lift b) (I.lift a)) (f i), proc f' -> do
     x1 <- integral' (p + 5) (Interval a m) -< f'
     x2 <- integral' (p + 5) (Interval m b) -< f'
     returnA -< I.add (p + 5) x1 x2)

forall_interval' :: (Show a, Rounded a) => Prec -> Interval a -> CMap (Interval a -> Bool) Bool
forall_interval' p i@(Interval a b) = CMap $ \f ->
  let m = R.average a b in
  -- traceShow p $
  (f i, proc f' -> do
    t1 <- forall_interval' (p + 5) (Interval a m) -< f'
    t2 <- forall_interval' (p + 5) (Interval m b) -< f'
    returnA -< t1 && t2)

exists_interval' :: (Show a, Rounded a) => Prec -> Interval a -> CMap (Interval a -> Bool) Bool
exists_interval' p i@(Interval a b) = CMap $ \f ->
  let m = R.average a b in
  -- traceShow p $
  (f (I.lift m), proc f' -> do
    t1 <- exists_interval' (p + 5) (Interval a m) -< f'
    t2 <- exists_interval' (p + 5) (Interval m b) -< f'
    returnA -< t1 || t2)

dedekind_cut' :: Rounded a => CMap (Interval a -> B) (Interval a)
dedekind_cut' = bound 1 R.one where
  bound p b = CMap $ \f -> let negb = R.neg p R.Down b in
    if fst (f (I.lift negb)) && snd (f (I.lift b))
      then let i = Interval negb b in (i, locate p i)
      else (I.realLine, bound (p + 1) (R.mulpow2 1 p R.Down b))
  locate p (Interval l u) = CMap $ \f ->
    let (l', u') = (let m = R.average l u in
                        case f (I.lift m) of
                          (True, _) -> (m, u)
                          (_, True) -> (l, m)
                          _ -> let mu = R.average m u in
                            case f (I.lift mu) of
                              (True, _) -> (mu, u)
                              (_, True) -> (l, mu)
                              _ -> (l, u))
    in let i' = Interval l' u' in (i', locate p i')

runCMap :: CMap () a -> [a]
runCMap (CMap f) = let (x, f') = f () in
  x : runCMap f'

integer :: Rounded r => Integer -> CMap g (Interval r)
integer i = withPrec $ \p _ -> I.rounded (\d -> R.ofInteger p d i)

rational :: Rounded r => Rational -> CMap g (Interval r)
rational q = ap2 RealExpr.div (integer (numerator q)) (integer (denominator q))

ap2 :: CMap (a, b) c -> CMap g a -> CMap g b -> CMap g c
ap2 f x y = f <<< x &&& y

ap1 :: CMap a b -> CMap g a -> CMap g b
ap1 f = (f <<<)

abs1 :: (forall d. CMap d g -> CMap d a -> CMap d b) -> CMap (g, a) b
abs1 f = f (arr fst) (arr snd)