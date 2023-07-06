{-|
A simple first-order language for exact real arithmetic,
based on a Zelus-like stream encoding.
`CMap a b` represents a continuous map from a space `a`
to a space `b`, where the Haskell types `a` and `b` represent
the types of finite approximations of those spaces.
For instance, `Interval MPFR` represents our usual real
number type.
-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving, DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Arrows #-}

module RealExpr where

import Prelude hiding (negate, signum, recip, div)
import Control.Category hiding ((.), id)
import qualified Control.Category as C
import Control.Arrow
import Data.Number.MPFR (MPFR)
import Data.IORef
import Data.MemoTrie
import Data.Ratio (numerator, denominator)
import Debug.Trace

import Interval (Interval (..))
import qualified Interval as I
import Rounded (Rounded, Prec, RoundDir (Up, Down))
import qualified Rounded as R

data CMap a b = CMap (a -> (b, CMap a b))
deriving instance Functor (CMap a)

type CPoint = CMap ()

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

bang :: CMap g ()
bang = arr (\_ -> ())

infty :: Rounded a => CMap g (Interval a)
infty = arr $ \_ -> I.lift (R.positiveInfinity)

toDiscrete :: Traversable t => t (CMap a b) -> CMap a (t b)
toDiscrete fs = CMap $ \x -> let res = fmap (\(CMap f) -> f x) fs in
  (fmap fst res, toDiscrete (fmap snd res))

parallel :: [CMap a b] -> CMap [a] [b]
parallel fs = CMap $ \xs -> let (rs, fs') = unzip (zipWith (\(CMap f) x -> f x) fs xs) in
  (rs, parallel fs')

parallelmt :: HasTrie i => (i -> CMap a b) -> CMap (i :->: a) (i :->: b)
parallelmt f = CMap $ \x ->
  let results = memo (\i -> let CMap f' = f i in f' (untrie x i)) in
  (trie (\i -> fst (results i)), parallelmt (memo (\i -> snd (results i))))

parallelmtg :: HasTrie i => (i -> CMap (g, a) b) -> CMap (g, i :->: a) (i :->: b)
parallelmtg f = CMap $ \(g, x) ->
  let results = memo (\i -> let CMap f' = f i in f' (g, untrie x i)) in
  (trie (\i -> fst (results i)), parallelmtg (memo (\i -> snd (results i))))

lift2mt :: HasTrie i => CMap (a, b) c -> CMap (i :->: a, i :->: b) (i :->: c)
lift2mt f = parallelmt (const f) <<< arr (\(x, y) -> trie (\i -> (untrie x i, untrie y i)))

tensor0 :: HasTrie i => CMap g a -> CMap g (i :->: a)
tensor0 f = fmap (trie . const) f

tensor1 :: HasTrie i => CMap a b -> CMap (i :->: a) (i :->: b)
tensor1 = parallelmt . const

tensor2 :: HasTrie i => HasTrie j => CMap (a, b) c -> CMap (i :->: a, j :->: b) ((i, j) :->: c)
tensor2 f = parallelmt (const f) <<< arr (\(x, y) -> trie (\(i, j) -> (untrie x i, untrie y j)))

replicateI :: CMap g a -> CMap g (i -> a)
replicateI = fmap const

curryTrie :: HasTrie i => HasTrie j => (i, j) :->: a -> i :->: (j :->: a)
curryTrie f = trie $ \i -> trie $ \j -> untrie f (i, j)

uncurryTrie :: HasTrie i => HasTrie j => i :->: (j :->: a) -> (i, j) :->: a
uncurryTrie f = trie $ \(i, j) -> untrie (untrie f i) j

class HasBottom a where
  bottom :: a

instance Rounded a => HasBottom (Interval a) where
  bottom = I.realLine

-- Not sure that this is right with the increasing precision in gab'
secondOrderPrim :: HasBottom a => CMap (a -> b) c -> CMap (g, a) b -> CMap g c
secondOrderPrim = secondOrderPrim' bottom

secondOrderPrim' :: a -> CMap (a -> b) c -> CMap (g, a) b -> CMap g c
secondOrderPrim' bot (CMap abc) (CMap gab) = CMap $ \g ->
    let (c, abc') = abc (\a -> let (b, gab') = gab (g, a) in b) in
    let (_, gab') = gab (g, bot) in
    (c, secondOrderPrim' bot abc' gab')

withPrec :: (Prec -> a -> b) -> CMap a b
withPrec f = withPrec' 32 where
  withPrec' p = CMap $ \x -> (f p x, withPrec' (p + 5))

withPrec2 :: (Prec -> a -> b -> c) -> CMap (a, b) c
withPrec2 op = withPrec $ \p (ix, iy) -> op p ix iy

{-| A typeclass for the structure of vector spaces
    needed for computing derivatives.
-}
class Additive v where
  zeroV  :: CMap g v         -- the zero vector
  addV   :: CMap (v, v) v    -- add vectors

instance Additive () where
  zeroV = arr (\_ -> ())
  addV = arr (\_ -> ())

instance (Additive u, Additive v) => Additive (u, v) where
  zeroV = zeroV &&& zeroV
  addV = proc ((u1, v1), (u2, v2)) -> do
    u <- addV -< (u1, u2)
    v <- addV -< (v1, v2)
    returnA -< (u, v)

class Additive a => CNum a where
  cadd, csub, cmul :: CMap (a, a) a
  cadd = addV
  cnegate, cabs, csignum :: CMap a a
  cfromInteger :: Integer -> CMap g a

class CNum a => CFractional a where
  cdiv :: CMap (a, a) a
  crecip :: CMap a a
  cfromRational :: Rational -> CMap g a
  cfromRational q = cdiv <<< cfromInteger (numerator q) &&& cfromInteger (denominator q)

class CFractional a => CFloating a where
  cpi :: CMap g a
  cexp, clog, csqrt, csin, ccos, ctan, casin, cacos, catan,
    csinh, ccosh, ctanh, casinh, cacosh, catanh,
    clog1p, cexpm1, clog1pexp, clog1mexp :: CMap a a
  clog1pexp = clog1p <<< cexp
  clog1mexp = clog1p <<< cnegate <<< cexp
  ctan = cdiv <<< csin &&& ccos

instance Rounded a => Additive (Interval a) where
  addV = add
  zeroV = integer 0

instance Rounded a => CNum (Interval a) where
  cadd = add
  cmul = mul
  cnegate = negate
  csub = sub
  cabs = RealExpr.max <<< (C.id &&& cnegate)
  cfromInteger = integer
  csignum = signum

instance Rounded a => CFractional (Interval a) where
  crecip = recip
  cdiv = div

add :: Rounded a => CMap (Interval a, Interval a) (Interval a)
add = withPrec2 I.add

sub :: Rounded a => CMap (Interval a, Interval a) (Interval a)
sub = withPrec2 I.sub

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

min :: Rounded a => CMap (Interval a, Interval a) (Interval a)
min = withPrec2 (\p -> I.min)

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

max_snd_deriv :: Rounded a => CMap (Interval a, Interval a) (Interval a)
max_snd_deriv = signum_deriv <<< sub

-- Maybe wastes some computation, but okay for now.
partialIfThenElse :: Rounded a => CMap g (Maybe Bool) -> CMap g (Interval a) -> CMap g (Interval a) -> CMap g (Interval a)
partialIfThenElse cond t f = proc g -> do
  c <- cond -< g
  tx <- t -< g
  fx <- f -< g
  returnA -< out c tx fx
  where
  out Nothing tr fa = I.union tr fa
  out (Just True) tr fa = tr
  out (Just False) tr fa = fa


max_deriv :: Rounded a => CMap ((Interval a, Interval a), (Interval a, Interval a)) (Interval a)
max_deriv = arr $ \((Interval xl xu, Interval yl yu), (dx, dy)) ->
  if xu < yl
    then dy
  else if yu < xl
    then dx
  else I.union dx dy

min_deriv :: Rounded a => CMap ((Interval a, Interval a), (Interval a, Interval a)) (Interval a)
min_deriv = arr $ \((Interval xl xu, Interval yl yu), (dx, dy)) ->
  if xu < yl
    then dx
  else if yu < xl
    then dy
  else I.union dx dy

type B = (Bool, Bool)

restrictReal :: Rounded a => CMap (Bool, Interval a) (Interval a)
restrictReal = arr $ \(s, x) -> if s then x else I.realLine

lt :: Rounded a => CMap (Interval a, Interval a) B
lt = arr (\(Interval l1 u1, Interval l2 u2) -> (u1 < l2, l1 > u2))

and :: CMap (B, B) B
and = arr (\((t1, f1), (t2, f2)) -> (t1 && t2, f1 || f2))

or :: CMap (B, B) B
or = arr (\((t1, f1), (t2, f2)) -> (t1 || t2, f1 && f2))

neg :: CMap B B
neg = arr (\(x, y) -> (y, x))

neq :: Rounded a => CMap (Interval a, Interval a) Bool
neq = arr $ \(Interval l1 u1, Interval l2 u2) -> u1 < l2 || u2 < l1

integral' :: Rounded a => Prec -> Interval a -> CMap (g, Interval a) (Interval a) -> CMap g (Interval a)
integral' p i@(Interval a b) (CMap f) = CMap $ \g ->
  let m = R.average a b in
  let (y, frefined) = f (g, i) in
  -- traceShow p $
  (I.mul p (I.sub p (I.lift b) (I.lift a)) y, proc g' -> do
     x1 <- integral' (p + 5) (Interval a m) frefined -< g'
     x2 <- integral' (p + 5) (Interval m b) frefined -< g'
     returnA -< I.add (p + 5) x1 x2)

integral1' :: Rounded a => CMap (g, Interval a) (Interval a) -> CMap g (Interval a)
integral1' = integral' 16 I.unitInterval

exists_interval' :: Rounded a => Prec -> Interval a -> CMap (g, Interval a) Bool -> CMap g Bool
exists_interval' p i@(Interval a b) (CMap f) = CMap $ \g ->
  let m = R.average a b in
  let (_, frefined) = f (g, i) in
  -- traceShow p $
  (fst (f (g, I.lift m)), proc g' -> do
    t1 <- exists_interval' (p + 5) (Interval a m) frefined -< g'
    t2 <- exists_interval' (p + 5) (Interval m b) frefined -< g'
    returnA -< t1 || t2)

recurseOnIntervals :: Rounded a => (b -> b -> b) -> Interval a -> CMap (g, Interval a) b -> CMap g b
recurseOnIntervals combine = go where
  go i@(Interval a b) (CMap f) = CMap $ \g ->
    let m = R.average a b in
    let (y, frefined) = f (g, i) in
    (y, proc g' -> do
      t1 <- go (Interval a m) frefined -< g'
      t2 <- go (Interval m b) frefined -< g'
      returnA -< combine t1 t2)

data Condition = Convex | Unknown | Done

maxargmaxIntervalsNewton :: forall g a. Rounded a => Interval a -> Word
  -> [(Condition, Interval a, CMap (g, Interval a) (Interval a, Interval a, Interval a))]
  -> CMap g (Interval a, Interval a)
maxargmaxIntervalsNewton origInterval p xs = CMap $ \g ->
  let ys = [ (b, x, f (g, x)) | (b, x, CMap f) <- xs ] in
  let maxyl = maximum [ yl | (_, _, ((Interval yl yh, _, _), _)) <- ys ] in
  let potentialxs = filter (\(_,_, ((Interval yl yh, _, _), _)) -> maxyl <= yh) ys in
  let argmaxi = foldr1 I.union [ i | (_, i, _) <- potentialxs ] in
  let maxi = foldr1 I.max [ y | (_, _, ((y, _, _), _)) <- potentialxs ] in
  ((argmaxi, maxi),
  maxargmaxIntervalsNewton origInterval (p + 5) (concatMap (refineIntervals g) potentialxs))
  where
  refineIntervals :: Rounded a => g -> (Condition, Interval a, ((Interval a, Interval a, Interval a), CMap (g, Interval a) (Interval a, Interval a, Interval a)))
    -> [(Condition, Interval a, CMap (g, Interval a) (Interval a, Interval a, Interval a))]
  refineIntervals g (Done, i, (_, f)) = [(Done, i, f)]
  refineIntervals g (Convex, i, (_, f)) = let (i', _) = newton_locate_step (fmap (\(y, y', y'') -> (y', y'')) f) p i g in
    -- hacky fix in case Newton iteration takes us outside of the original interval that we're argmaxing over.
    let (newstate, i'') = if I.lower i' > I.upper origInterval then (Done, I.lift (I.upper origInterval))
        else if I.upper i' < I.lower origInterval then (Done, I.lift (I.lower origInterval))
        else (Convex, i')
    in [(newstate, i'', f)]
  refineIntervals g (Unknown, i, yf@((_, _, Interval f''l f''h), f)) =
     if f''h < R.zero then refineIntervals g (Convex, i, yf)
                      else let (i1, i2) = I.split i in [(Unknown, i1, f), (Unknown, i2, f)]

argmaxIntervalsNewton origInterval p xs =
  fmap fst $ maxargmaxIntervalsNewton origInterval p xs

maxIntervalsNewton origInterval p xs =
  fmap snd $ maxargmaxIntervalsNewton origInterval p xs

argmaxIntervals :: Rounded a => [(Interval a, CMap (g, Interval a) (Interval a))] -> CMap g (Interval a)
argmaxIntervals xs = CMap $ \g ->
  let ys = [ (x, f (g, x)) | (x, CMap f) <- xs ] in
  let maxyl = maximum [ yl | (_, (Interval yl yh, _)) <- ys ] in
  let potentialxs = filter (\(_, (Interval yl yh, _)) -> maxyl <= yh) ys in
  (foldr1 I.union (map fst potentialxs),
  argmaxIntervals [ (i, f) | (i, (_, f)) <- splitIntervals potentialxs ])

-- almost the same as argmaxIntervals, I should abstract it out
maxIntervals :: Rounded a => [(Interval a, CMap (g, Interval a) (Interval a))] -> CMap g (Interval a)
maxIntervals xs = CMap $ \g ->
  let ys = [ (x, f (g, x)) | (x, CMap f) <- xs ] in
  let maxyl = maximum [ yl | (_, (Interval yl yh, _)) <- ys ] in
  let potentialxs = filter (\(_, (Interval yl yh, _)) -> maxyl <= yh) ys in
  (foldr1 I.max (map (fst . snd) potentialxs),
  maxIntervals [ (i, f) | (i, (_, f)) <- splitIntervals potentialxs ])

argminIntervals :: Rounded a => [(Interval a, CMap (g, Interval a) (Interval a))] -> CMap g (Interval a)
argminIntervals xs = CMap $ \g ->
  let ys = [ (x, f (g, x)) | (x, CMap f) <- xs ] in
  let minyh = minimum [ yh | (_, (Interval yl yh, _)) <- ys ] in
  let potentialxs = filter (\(_, (Interval yl yh, _)) -> yl <= minyh) ys in
  (foldr1 I.union (map fst potentialxs),
  argminIntervals [ (i, f) | (i, (_, f)) <- splitIntervals potentialxs ])

-- almost the same as argminIntervals, I should abstract it out
minIntervals :: Rounded a => [(Interval a, CMap (g, Interval a) (Interval a))] -> CMap g (Interval a)
minIntervals xs = CMap $ \g ->
  let ys = [ (x, f (g, x)) | (x, CMap f) <- xs ] in
  let minyh = minimum [ yh | (_, (Interval yl yh, _)) <- ys ] in
  let potentialxs = filter (\(_, (Interval yl yh, _)) -> yl <= minyh) ys in
  (foldr1 I.min (map (fst . snd) potentialxs),
  minIntervals [ (i, f) | (i, (_, f)) <- splitIntervals potentialxs ])

-- Split all of the intervals in the list into two and concatenate them all together.
splitIntervals :: Rounded a => [(Interval a, b)] -> [(Interval a, b)]
splitIntervals xs = [ (i', x) | (i, x) <- xs, i' <- let (i1, i2) = I.split i in [i1, i2]]

forallIntervals :: Rounded a => [(Interval a, CMap (g, Interval a) Bool)] -> CMap g Bool
forallIntervals xs = CMap $ \g ->
  let notyetTrue = [ (x, fnew) | (x, CMap f) <- xs, let (y, fnew) = f (g, x), not y ] in
  (null notyetTrue, forallIntervals (splitIntervals notyetTrue))

argmax_interval' :: Rounded a => Interval a -> CMap (g, Interval a) (Interval a) -> CMap g (Interval a)
argmax_interval' i f = argmaxIntervals [(i, f)]

argmax_interval_newton' :: Rounded a => Interval a -> CMap (g, Interval a) (Interval a, Interval a, Interval a)
  -> CMap g (Interval a)
argmax_interval_newton' i f = argmaxIntervalsNewton i 16 [(Unknown, i, f)]

max_interval_newton' :: Rounded a => Interval a -> CMap (g, Interval a) (Interval a, Interval a, Interval a)
  -> CMap g (Interval a)
max_interval_newton' i f = maxIntervalsNewton i 16 [(Unknown, i, f)]

argmin_interval' :: Rounded a => Interval a -> CMap (g, Interval a) (Interval a) -> CMap g (Interval a)
argmin_interval' i f = argminIntervals [(i, f)]

forall_interval' :: Rounded a => Interval a -> CMap (g, Interval a) Bool -> CMap g Bool
forall_interval' i f = forallIntervals [(i, f)]

max_interval' :: Rounded a => Interval a -> CMap (g, Interval a) (Interval a) -> CMap g (Interval a)
max_interval' i f = maxIntervals [(i, f)]

min_interval' :: Rounded a => Interval a -> CMap (g, Interval a) (Interval a) -> CMap g (Interval a)
min_interval' i f = minIntervals [(i, f)]

dedekind_cut' :: Rounded a => CMap (Interval a -> B) (Interval a)
dedekind_cut' = bound 1 R.one where
  bound p b = CMap $ \f -> let negb = R.neg p R.Down b in
    if fst (f (I.lift negb)) && snd (f (I.lift b))
      then let i = Interval negb b in (i, loc p i)
      else (I.realLine, bound (p + 1) (R.mulpow2 1 p R.Down b))
  loc p i = CMap $ \f -> let i' = locate p i f in
    (i', loc (p + 5) i')

locate :: Rounded a => Word -> Interval a -> (Interval a -> B) -> Interval a
locate p (Interval l u) f =
  let (l', u') = (let m = R.average l u in
                      case f (I.lift m) of
                        (True, _) -> (m, u)
                        (_, True) -> (l, m)
                        _ -> let mu = R.average m u in
                          case f (I.lift mu) of
                            (True, _) -> (mu, u)
                            (_, True) -> (l, mu)
                            _ -> (l, u))
  in Interval l' u'

runPoint :: CPoint a -> [a]
runPoint (CMap f) = let (x, f') = f () in
  x : runPoint f'

integer :: Rounded r => Integer -> CMap g (Interval r)
integer i = withPrec $ \p _ -> I.rounded (\d -> R.ofInteger p d i)

abs1 :: (forall d. CMap d g -> CMap d a -> CMap d b) -> CMap (g, a) b
abs1 f = f (arr fst) (arr snd)

firstRoot :: Rounded a => CMap (Interval a -> B) (Interval a)
firstRoot = rootAtP 1 (Interval R.zero R.one) where
  rootAtP p i@(Interval l u) = CMap $ \f -> let m = R.average l u in
    if fst (f (Interval l m)) -- the left interval is to the left of the point
      then let i' = (Interval m u) in (i', rootAtP p i') -- refine the right interval
      else if snd (f (I.lift m)) -- the middle of the interval is to the right of the point
        then let i' = (Interval l m) in (i', rootAtP p i') -- refine the left
      else let i' = (computeOverSubintervals f (splitIntervals p i)) in (i', rootAtP (p + 1) i') -- refine everything!

  -- Split the given interval into 2^k intervals
  splitIntervals :: Rounded a => Int -> Interval a -> [Interval a]
  splitIntervals k i@(Interval l u) = if k==0 then [i]
                                        else let m = R.average l u in
                                          (splitIntervals (k - 1) (Interval l m)) ++
                                          (splitIntervals (k - 1) (Interval m u))

  computeOverSubintervals f intervals = let prefix = (removeBeginning f intervals) in
    (Interval (I.lower (head prefix)) (I.upper (removeEnd f prefix)))

  removeBeginning :: Rounded a => (Interval a -> B) -> [Interval a] -> [Interval a]
  removeBeginning f intervals = case intervals of
      [i] -> [i]
      is -> if fst (f (head is))
              then (removeBeginning f (tail is))
              else is

  removeEnd :: Rounded a => (Interval a -> B) -> [Interval a] -> Interval a
  removeEnd f intervals = case intervals of
    [i] -> i
    is -> if snd (f (I.lift (R.average (I.lower (last is)) (I.upper (last is)))))
                            then (head is)
                            else (removeEnd f (init is))

-- We already have a bounded interval where the result is known to lie.
newton_locate :: Rounded r => CMap (g, Interval r) (Interval r, Interval r)
  -> Word -> Interval r -> CMap g (Interval r)
newton_locate f p i = CMap $ \g ->
    let (i', frefined) = newton_locate_step f p i g in
    (i', newton_locate frefined (p + 5) i')

newton_locate_step ::  Rounded r => CMap (g, Interval r) (Interval r, Interval r)
  -> Word -> Interval r -> g -> (Interval r, CMap (g, Interval r) (Interval r, Interval r))
newton_locate_step (CMap f) p i@(Interval l u) = \g ->
    let ((fx1, _), _) = f (g, I.lift l) in
    let ((fx2, _), _) = f (g, I.lift u) in
    let ((_, f'x), frefined) = f (g, i) in
    let i1 = I.sub p (I.lift l) (I.div p fx1 f'x) in
    let i2 = I.sub p (I.lift u) (I.div p fx2 f'x) in
    let i' = i `I.join` i1 `I.join` i2 in
    (
    if I.lower i' > I.lower i || I.upper i' < I.upper i -- we made progress
      then i'
      else locate p i (\x -> let Interval a b = fst (fst (f (g, x))) in (a > R.zero, b < R.zero))
    , frefined)

newton_cut' :: Rounded r => CMap (g, Interval r) (Interval r, Interval r)
  -> CMap g (Interval r)
newton_cut' f = bound 1 1 R.one where
  bound n p b = CMap $ \g -> let negb = R.neg p R.Down b in
    if I.lower (fst (fst (nsteps n f (g, I.lift negb)))) > R.zero && I.upper (fst (fst (nsteps n f (g, I.lift b)))) < R.zero
      then let i = Interval negb b in (i, newton_locate f p i)
      else (I.realLine, bound (n + 1) (p + 1) (R.mulpow2 1 p R.Down b))

newton_cut'_with_bounds :: Rounded r =>
     CMap g (Interval r)
  -> CMap g (Interval r)
  -> CMap (g, Interval r) (Interval r, Interval r)
  -> CMap g (Interval r)
newton_cut'_with_bounds lowerf upperf f = newton_locate' lowerf upperf f 1 I.realLine
  where
  newton_locate' (CMap lower) (CMap upper) f p (Interval a b) = CMap $ \g ->
    let (Interval l _, lower') = lower g in
    let (Interval _ u, upper') = upper g in
    let (i', frefined) = newton_locate_step f p (Interval (Prelude.max l a) (Prelude.min u b)) g in
    (i', newton_locate' lower' upper' frefined (p + 5) i')

-- Get more precision out of a continuous map by running it many times.
nsteps :: Int -> CMap a b -> a -> (b, CMap a b)
nsteps 1 (CMap f) x = f x
nsteps n (CMap f) x = let (_, f') = f x in nsteps (n - 1) f' x

-- Is `argmax01 f` "distinctly" at an endpoint, i.e.,
-- argmax01 f = 0 and f'(0) < 0    OR
-- argmax01 f = 1 and f'(1) > 0?
-- If so, then Just True.
-- If clearly not, then Just False
-- If we can't tell, then Nothing.
argoptIntervalAtEnd :: Rounded r => (Interval r -> forall g. CMap (g, Interval r) z -> CMap g (Interval r)) ->
  CMap z (Interval r) -> Interval r -> CMap (g, Interval r) z -> CMap g (Maybe Bool)
argoptIntervalAtEnd argopt_interval' getDeriv i ff' = proc g -> do
  curArgopt <- argopt_interval' i ff' -< g
  func (getDeriv <<< ff') -< (g, curArgopt)
  where
  func (CMap f') = CMap $ \(g, curArgopt) ->
    let (f'x, refinedf') = f' (g, curArgopt) in
      (if I.lower curArgopt > I.lower i && I.upper curArgopt < I.upper i
        then Just False
        else
        if I.lower f'x > R.zero || I.upper f'x < R.zero
          then Just True
          else Nothing, func refinedf')

argmaxIntervalAtEnd, argminIntervalAtEnd :: Rounded r => Interval r -> CMap (g, Interval r) (Interval r, Interval r) -> CMap g (Maybe Bool)
argmaxIntervalAtEnd = argoptIntervalAtEnd (\i f -> argmax_interval' i (fmap fst f)) (arr snd)
argminIntervalAtEnd = argoptIntervalAtEnd (\i f -> argmin_interval' i (fmap fst f)) (arr snd)

argmaxNewtonIntervalAtEnd :: Rounded r => Interval r -> CMap (g, Interval r) (Interval r, Interval r, Interval r) -> CMap g (Maybe Bool)
argmaxNewtonIntervalAtEnd = argoptIntervalAtEnd argmax_interval_newton' (arr (\(y, y', y'') -> y'))

-- I have no idea whether these are sensible
collapse :: CMap a (CMap b c) -> CMap (a, b) c
collapse (CMap f) = CMap $ \(a, b) ->
  let (CMap g, f') = f a in
  let (c, g') = g b in
  (c, collapse f')

uncollapse :: CMap (a, b) c -> CMap a (CMap b c)
uncollapse f = CMap $ \a ->
  (g f a, uncollapse f)
  where
  g (CMap z) a = CMap $ \b -> let (c, z') = z (a, b) in (c, g z' a)