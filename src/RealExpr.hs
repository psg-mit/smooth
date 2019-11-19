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

-- Not sure that this is right with the increasing precision in gab'
secondOrderPrim :: CMap (a -> b) c -> CMap (g, a) b -> CMap g c
secondOrderPrim (CMap abc) (CMap gab) = CMap $ \g ->
    let (c, abc') = abc (\a -> let (b, gab') = gab (g, a) in b) in
    let (_, gab') = gab (g, undefined) in
    (c, secondOrderPrim abc' gab')

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
  cabs = error "TBD"
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

integral' :: Rounded a => Prec -> Interval a -> CMap (Interval a -> Interval a) (Interval a)
integral' p i@(Interval a b) = CMap $ \f ->
  let m = R.average a b in
  -- traceShow p $
  (I.mul p (I.sub p (I.lift b) (I.lift a)) (f i), proc f' -> do
     x1 <- integral' (p + 5) (Interval a m) -< f'
     x2 <- integral' (p + 5) (Interval m b) -< f'
     returnA -< I.add (p + 5) x1 x2)

integral1' :: R.Rounded a => CMap (g, Interval a) (Interval a) -> CMap g (Interval a)
integral1' = secondOrderPrim (integral' 16 I.unitInterval)

exists_interval' :: Rounded a => Prec -> Interval a -> CMap (Interval a -> Bool) Bool
exists_interval' p i@(Interval a b) = CMap $ \f ->
  let m = R.average a b in
  -- traceShow p $
  (f (I.lift m), proc f' -> do
    t1 <- exists_interval' (p + 5) (Interval a m) -< f'
    t2 <- exists_interval' (p + 5) (Interval m b) -< f'
    returnA -< t1 || t2)

recurseOnIntervals :: Rounded a => (b -> b -> b) -> Prec -> Interval a -> CMap (Interval a -> b) b
recurseOnIntervals combine = go where
  go p i@(Interval a b) = CMap $ \f ->
    let m = R.average a b in
    (f (I.lift m), proc f' -> do
      t1 <- go (p + 5) (Interval a m) -< f'
      t2 <- go (p + 5) (Interval m b) -< f'
      returnA -< combine t1 t2)

forall_interval' :: Rounded a => Prec -> Interval a -> CMap (Interval a -> Bool) Bool
forall_interval' = recurseOnIntervals (&&)

max_interval' :: Rounded a => Prec -> Interval a -> CMap (Interval a -> Interval a) (Interval a)
max_interval' = recurseOnIntervals I.max

min_interval' :: Rounded a => Prec -> Interval a -> CMap (Interval a -> Interval a) (Interval a)
min_interval' = recurseOnIntervals I.min

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


-- Assumption: f is monotone decreasing and has a single isolated root.
newton_cut' :: Rounded r => CMap (Interval r -> (Interval r, Interval r)) (Interval r)
newton_cut' = bound 1 R.one where
  bound :: Rounded r => Word -> r -> CMap (Interval r -> (Interval r, Interval r)) (Interval r)
  bound p b = CMap $ \f -> let negb = R.neg p R.Down b in
    if I.lower (fst (f (I.lift negb))) > R.zero && I.upper (fst (f (I.lift b))) < R.zero
      then let i = Interval negb b in (i, loc p i)
      else (I.realLine, bound (p + 1) (R.mulpow2 1 p R.Down b))
  loc p i@(Interval l u) = CMap $ \f ->
    let (fx1, _) = f (I.lift l) in
    let (fx2, _) = f (I.lift u) in
    let (_, f'x) = f i in
    let i1 = I.sub p (I.lift l) (I.div p fx1 f'x) in
    let i2 = I.sub p (I.lift u) (I.div p fx2 f'x) in
    let i' = i `I.join` i1 `I.join` i2 in
    if I.lower i' > I.lower i || I.upper i' < I.upper i -- we made progress
      then (i', loc (p + 5) i')
      else let i' = locate p i (\x -> let Interval a b = fst (f x) in (a > R.zero, b < R.zero))
           in (i', loc (p + 5) i')




-- I have no idea whether any of these are sensible
collapse1 :: CMap a (b -> c) -> CMap (a, b) c
collapse1 (CMap f) = CMap $ \(a, b) ->
  let (bc, f') = f a in
  (bc b, collapse1 f')

uncollapse1 :: CMap (a, b) c -> CMap a (b -> c)
uncollapse1 (CMap f) = CMap $ \a ->
  (\b -> let (c, f') = f (a, b) in c, let (_, f') = f (a, undefined) in uncollapse1 f')

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