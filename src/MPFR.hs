{-|
Exact real arithmetic implementations, based on MPFR implementations,
of various special functions.
-}

{-# LANGUAGE FlexibleInstances #-}

module MPFR where

import Control.Arrow (first, arr)
import Prelude hiding (Real)
import qualified Interval as I
import Interval (Interval (..))
import RealExpr
import Expr (ap1, ap2, dedekind_cut, exists_unit_interval, isTrue )
import Rounded as R
import qualified Data.Number.MPFR as M
import qualified Language.Haskell.HsColour.ANSI as C
import GHC.Float
import Debug.Trace
import Data.Number.MPFR (MPFR)

roundDirMPFR :: RoundDir -> M.RoundMode
roundDirMPFR Up = M.Up
roundDirMPFR Down = M.Down

instance Rounded M.MPFR where
  add p d = M.add (roundDirMPFR d) (fromIntegral p)
  sub p d = M.sub (roundDirMPFR d) (fromIntegral p)
  mul p d = M.mul (roundDirMPFR d) (fromIntegral p)
  div p d = M.div (roundDirMPFR d) (fromIntegral p)
  pow p d x k = M.powi (roundDirMPFR d) (fromIntegral p) x k
  negativeInfinity = M.setInf 0 (-1)
  positiveInfinity = M.setInf 0 1
  zero = M.zero
  one = M.one
  min a b = case M.cmp a b of
    Just LT -> a
    Just _ -> b
     -- NaN gives Nothing! Not sure if this is the right thing to do
    Nothing -> M.minD  M.Down (M.getPrec a `Prelude.max` M.getPrec b) a b
  max a b = case M.cmp a b of
    Just GT -> a
    Just _ -> b
     -- NaN gives Nothing! Not sure if this is the right thing to do
    Nothing -> M.minD M.Down (M.getPrec a `Prelude.max` M.getPrec b) a b
  min' p d = M.minD (roundDirMPFR d) (fromIntegral p)
  max' p d = M.maxD (roundDirMPFR d) (fromIntegral p)
  neg p d = M.neg (roundDirMPFR d) (fromIntegral p)
  average a b = let p = (M.getPrec a `Prelude.max` M.getPrec b) + 1 in
    M.mul2i M.Near (fromIntegral p) (M.add M.Near p a b) (-1)
  mulpow2 i p d x = M.mul2i (roundDirMPFR d) (fromIntegral p) x i
  ofInteger p d = M.fromIntegerA (roundDirMPFR d) (fromIntegral p)
  negativeOne = ofInteger 10 Down (-1)
  isInfinity = M.isInfinite
  isZero = M.isZero
  ofString p d = M.stringToMPFR (roundDirMPFR d) (fromIntegral p) 10
  toString x =
    let exp_notation = 4 in
    let trim = False in
      if M.isNumber x then
        let (s, e) = M.mpfrToString M.Near 0 10 x in
        let e' = fromIntegral e in
        let (sign, str') = if s !! 0 == '-' then ("-", tail s) else ("", s)
        in
        let str = if trim then trim_right (Prelude.max 1 e') str'  '0' else str'
        in
          if e' > length str || e' < - exp_notation then
            sign ++ string_insert str 1 "." ++ "e" ++ show (e' - 1)
          else if e > 0 then
            sign ++ string_insert str e' "."
          else
            sign ++ "0." ++ replicate (-e') '0' ++ str
      else
      if M.isNaN x then "NaN"
      else if M.greater x M.zero
        then "+Infinity"
        else "-Infinity"

trim_right :: Int -> String -> Char -> String
trim_right min_length s c = let (s1, s2) = splitAt min_length s in
  s1 ++ trimAllChar c s2

trimAllChar :: Char -> String -> String
trimAllChar c = reverse . dropWhile (== c) . reverse

string_insert :: String -> Int -> String -> String
string_insert s i toInsert = let (s1, s2) = splitAt i s in
  s1 ++ toInsert ++ s2

type Real = Interval M.MPFR

monotone :: (M.RoundMode -> M.Precision -> M.MPFR -> M.MPFR) -> CMap Real Real
monotone f = withPrec $ \p -> I.monotone (\d x -> f (roundDirMPFR d) (fromIntegral p) x)

antitone :: (M.RoundMode -> M.Precision -> M.MPFR -> M.MPFR) -> CMap Real Real
antitone f = withPrec $ \p -> I.monotone (\d x -> f (roundDirMPFR d) (fromIntegral p) x) . I.flip

constant :: (M.RoundMode -> M.Precision -> M.MPFR) -> CMap g Real
constant f = withPrec $ \p _ -> I.rounded (\d -> f (roundDirMPFR d) (fromIntegral p))


-- Many monotone functions

exp2' :: CMap Real Real
exp2' = monotone M.exp2

exp2 :: CMap g Real -> CMap g Real
exp2 = ap1 exp2'

exp10' :: CMap Real Real
exp10' = monotone M.exp10

exp10 :: CMap g Real -> CMap g Real
exp10 = ap1 exp10'

log2' :: CMap Real Real
log2' = monotone M.log2

log2 :: CMap g Real -> CMap g Real
log2 = ap1 log2'

log10' :: CMap Real Real
log10' = monotone M.log10

log10 :: CMap g Real -> CMap g Real
log10 = ap1 log10'

-- log1p :: CMap g Real -> CMap g Real
-- log1p = ap1 log1p'

expm1 :: CMap g Real -> CMap g Real
expm1 = ap1 cexpm1

-- Constants

log2c :: CMap g Real
log2c = constant M.log2c

euler :: CMap g Real
euler = constant M.euler

catalan :: CMap g Real
catalan = constant M.catalan

sinI :: M.Precision -> Real -> Real
sinI prec i@(I.Interval a b)
  | R.ofInteger (fromIntegral prec) R.Down 3 < I.lower (I.width (fromIntegral prec) i)
    = I.Interval R.negativeOne R.one
  | not (R.negative deriva1) && not (R.negative derivb1)
    = sinMonotone i
  | not (R.positive deriva2) && not (R.positive derivb2)
    = sinMonotone (I.flip i)
  | not (R.negative deriva1) && not (R.positive derivb2)
    = I.Interval (R.min (M.sin M.Down prec a) (M.sin M.Down prec b))
          R.one
  | not (R.positive deriva1) && not (R.negative derivb2)
    = I.Interval R.negativeOne
         (R.max (M.sin M.Up prec a) (M.sin M.Up prec b))
  | otherwise{- Not sure about the sign of either of the derivatives -}
    = I.Interval R.negativeOne R.one
  where
  sinMonotone = I.monotone (\d -> M.sin (roundDirMPFR d) prec)
  I.Interval deriva1 deriva2 = I.rounded (\d -> M.cos (roundDirMPFR d) prec a)
  I.Interval derivb1 derivb2 = I.rounded (\d -> M.cos (roundDirMPFR d) prec b)

cosI :: M.Precision -> Real -> Real
cosI prec i@(I.Interval a b)
  | R.ofInteger (fromIntegral prec) R.Down 3 < I.lower (I.width (fromIntegral prec) i)
    = I.Interval R.negativeOne R.one
  | not (R.positive negderiva1) && not (R.positive negderivb1)
    = cosMonotone i
  | not (R.negative negderiva2) && not (R.negative negderivb2)
    = cosMonotone (I.flip i)
  | not (R.positive negderiva1) && not (R.negative negderivb2)
    = I.Interval (R.min (M.cos M.Down prec a) (M.cos M.Down prec b))
          R.one
  | not (R.negative negderiva1) && not (R.positive negderivb2)
    = I.Interval R.negativeOne
          (R.max (M.cos M.Up prec a) (M.cos M.Up prec b))
  | otherwise{- Not sure about the sign of either of the derivatives -}
    = I.Interval R.negativeOne R.one
  where
  cosMonotone = I.monotone (\d -> M.cos (roundDirMPFR d) prec)
  I.Interval negderiva1 negderiva2 = I.rounded (\d -> M.sin (roundDirMPFR d) prec a)
  I.Interval negderivb1 negderivb2 = I.rounded (\d -> M.sin (roundDirMPFR d) prec b)

coshI :: M.Precision -> Real -> Real
coshI prec i@(I.Interval a b)
  | R.positive a = coshi
  | R.negative b = I.flip coshi
  | otherwise    = I.Interval R.one (R.max' (fromIntegral prec) R.Up ca cb)
  where
  coshi@(I.Interval ca cb) = I.monotone (\d -> M.cosh (roundDirMPFR d) prec) i

fact :: Word -> CMap g Real
fact n = constant (\d p -> M.facw d p n)

-- TODO: implement tan
instance CFloating Real where
  cpi = constant M.pi
  cexp = monotone M.exp
  clog = monotone M.log
  csqrt = monotone M.sqrt
  csinh = monotone M.sinh
  ctanh = monotone M.tanh
  csin = withPrec (sinI . fromIntegral)
  ccos = withPrec (cosI . fromIntegral)
  ccosh = withPrec (coshI . fromIntegral)
  -- NOTE: produces NaN when given inputs out of range
  casin = monotone M.asin
  catan = monotone M.atan
  casinh = monotone M.asinh
  cacosh = monotone M.acosh
  catanh = monotone M.atanh
  -- Monotone decreasing (antitone) functions
  cacos = antitone M.acos
  -- log,exp,etc.
  clog1p = monotone M.log1p
  cexpm1 = monotone M.expm1


match :: String -> String -> (String, String)
match a@(x : xs) (y : ys) = if x == y then first (x :) (match xs ys) else ([], a)
match [] _ = ([], [])
match _ [] = ([], [])

extendFromTo :: String -> String -> (Int, String)
extendFromTo a@(x : xs) b@(y : ys) = if x == y then extendFromTo xs ys else (length a, b)
extendFromTo [] ys = (0, ys)
extendFromTo xs [] = (length xs, "")


data RootResult = NoRoot | Root (Interval MPFR) | Undetermined (Interval MPFR) deriving Show

firstRoot :: CMap (Interval MPFR -> B) RootResult
firstRoot = rootAtP 1 (Undetermined (Interval M.zero M.one)) where

  -- Search for a root at precision p.
  rootAtP p (Undetermined i) = CMap $ \f ->
    if (I.lower i > M.zero) && (I.upper i < M.one)
      then (Root i, rootAtP p (Root i))
    else
      let interval = refineInterval f p i in
      case interval of
        Nothing -> (NoRoot, rootAtP p NoRoot)
        Just i' -> (Undetermined i', rootAtP (p+1) (Undetermined i'))

  -- If there is no root in [0, 1], there will never be a root!
  rootAtP p NoRoot = arr $ \f -> NoRoot

  -- Keep refining the root.
  rootAtP p (Root i@(Interval l u)) = CMap $ \f ->
    let Just i' = refineInterval f p i in
    (Root i', rootAtP (p+1) (Root i'))

  refineInterval f p i = computeOverSubintervals f (splitIntervals p i)

  -- Split the given interval into 2^k intervals
  splitIntervals :: Int -> Interval MPFR -> [Interval MPFR]
  splitIntervals k i@(Interval l u) =
    if k==0 then [i]
    else let m = average l u in
      (splitIntervals (k - 1) (Interval l m)) ++ (splitIntervals (k - 1) (Interval m u))

  computeOverSubintervals :: (Interval MPFR -> B) -> [Interval MPFR] -> Maybe (Interval MPFR)
  computeOverSubintervals f intervals =
    let prefix = (removeBeginning f intervals) in
      case prefix of
        [] -> Nothing
        is ->
          let end = removeEnd f (tail is) in
            case end of
              [] -> if snd (f (head is)) then Nothing else Just (head is)
              end_is -> Just (Interval (I.lower (head is)) (I.upper (last end_is)))

  removeBeginning :: (Interval MPFR -> B) -> [Interval MPFR] -> [Interval MPFR]
  removeBeginning f intervals = case intervals of
      [] -> []
      is -> if fst (f (head is))
              then (removeBeginning f (tail is))
              else is

  removeEnd :: (Interval MPFR -> B) -> [Interval MPFR] -> [Interval MPFR]
  removeEnd f intervals = case intervals of
    [] -> []
    _  -> if snd (f (I.lift (I.lower (head intervals))))
            then []
            else (head intervals):(removeEnd f (tail intervals))


firstRoot1 :: (CMap (g, Interval MPFR) B) -> CMap g RootResult
firstRoot1 f = secondOrderPrim firstRoot f

-- this code is really gross
showIntervals :: [Real] -> String
showIntervals = go "" ""
  where
  hl = C.highlight [C.Foreground C.Red]
  go certain tentative (i : xs) = let (nextCertain, nextTentative) = forInterval i in
    let (backtrackCertain, newCertain) = extendFromTo certain nextCertain in
    (if backtrackCertain == 0 && null newCertain
      then let (backtrackTentative, newTentative) = extendFromTo tentative nextTentative in
           concat (replicate backtrackTentative C.cursorLeft) ++ hl newTentative
      else concat (map (\_ -> C.cursorLeft) tentative ++ replicate backtrackCertain C.cursorLeft) ++ newCertain ++ hl nextTentative) ++ go nextCertain nextTentative xs

  mpfrInfo round x = let (s, e) = M.mpfrToString round 0 10 x in
    let e' = fromIntegral e in
    if s !! 0 == '-' then (False, tail s, e') else (True, s, e')

  forInterval i@(I.Interval l h) = if M.isInfinite l || M.isInfinite h
    then ("", show i) else
    if signl == signh
    then first (("e" ++ show e' ++ (if signl then " " else " -") ++ ".") ++) (match sl' sh')
    else ("", "0 (e" ++ show e' ++ ")")
    where
    (signl, sl, el) = mpfrInfo M.Down l
    (signh, sh, eh) = mpfrInfo M.Up h
    (sl', sh', e') = packZeros (sl, el) (sh, eh)

  packZeros (sl, el) (sh, eh) = if el <= eh
    then (replicate (eh - el) '0' ++ sl, sh, eh)
    else (sl, replicate (el - eh) '0' ++ sh, el)

printReal :: CPoint Real -> IO ()
printReal = putStrLn . showIntervals . runPoint