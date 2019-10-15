{-|
Exact real arithmetic implementations, based on MPFR implementations,
of various special functions.
-}

{-# LANGUAGE FlexibleInstances #-}

module MPFR where

import Prelude
import qualified Interval as I
import Interval (Interval)
import RealExpr
import Expr ()
import qualified Rounded as R
import qualified Data.Number.MPFR as M

type R = Interval M.MPFR

monotone :: (M.RoundMode -> M.Precision -> M.MPFR -> M.MPFR) -> CMap R R
monotone f = withPrec $ \p -> I.monotone (\d x -> f (R.roundDirMPFR d) (fromIntegral p) x)

antitone :: (M.RoundMode -> M.Precision -> M.MPFR -> M.MPFR) -> CMap R R
antitone f = withPrec $ \p -> I.monotone (\d x -> f (R.roundDirMPFR d) (fromIntegral p) x) . I.flip

constant :: (M.RoundMode -> M.Precision -> M.MPFR) -> CMap g R
constant f = withPrec $ \p _ -> I.rounded (\d -> f (R.roundDirMPFR d) (fromIntegral p))


-- Many monotone functions

exp' :: CMap R R
exp' = monotone M.exp

exp2' :: CMap R R
exp2' = monotone M.exp2

exp2 :: CMap g R -> CMap g R
exp2 = ap1 exp2'

exp10' :: CMap R R
exp10' = monotone M.exp10

exp10 :: CMap g R -> CMap g R
exp10 = ap1 exp10'

log' :: CMap R R
log' = monotone M.log

log2' :: CMap R R
log2' = monotone M.log2

log2 :: CMap g R -> CMap g R
log2 = ap1 log2'

log10' :: CMap R R
log10' = monotone M.log10

log10 :: CMap g R -> CMap g R
log10 = ap1 log10'

log1p' :: CMap R R
log1p' = monotone M.log1p

log1p :: CMap g R -> CMap g R
log1p = ap1 log1p'

expm1' :: CMap R R
expm1' = monotone M.expm1

expm1 :: CMap g R -> CMap g R
expm1 = ap1 expm1'

sqrt' :: CMap R R
sqrt' = monotone M.sqrt

sinh' :: CMap R R
sinh' = monotone M.sinh

tanh' :: CMap R R
tanh' = monotone M.tanh

-- NOTE: produces NaN when given inputs out of range
asin' :: CMap R R
asin' = monotone M.asin

atan' :: CMap R R
atan' = monotone M.atan

asinh' :: CMap R R
asinh' = monotone M.asinh

acosh' :: CMap R R
acosh' = monotone M.acosh

atanh' :: CMap R R
atanh' = monotone M.atanh



-- Monotone decreasing (antitone) functions
acos' :: CMap R R
acos' = antitone M.acos

-- Constants

log2c :: CMap g R
log2c = constant M.log2c

euler :: CMap g R
euler = constant M.euler

catalan :: CMap g R
catalan = constant M.catalan

sinI :: M.Precision -> Interval M.MPFR -> Interval M.MPFR
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
  sinMonotone = I.monotone (\d -> M.sin (R.roundDirMPFR d) prec)
  I.Interval deriva1 deriva2 = I.rounded (\d -> M.cos (R.roundDirMPFR d) prec a)
  I.Interval derivb1 derivb2 = I.rounded (\d -> M.cos (R.roundDirMPFR d) prec b)

sin' :: CMap R R
sin' = withPrec (sinI . fromIntegral)

cosI :: M.Precision -> Interval M.MPFR -> Interval M.MPFR
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
  cosMonotone = I.monotone (\d -> M.cos (R.roundDirMPFR d) prec)
  I.Interval negderiva1 negderiva2 = I.rounded (\d -> M.sin (R.roundDirMPFR d) prec a)
  I.Interval negderivb1 negderivb2 = I.rounded (\d -> M.sin (R.roundDirMPFR d) prec b)

cos' :: CMap R R
cos' = withPrec (cosI . fromIntegral)

coshI :: M.Precision -> Interval M.MPFR -> Interval M.MPFR
coshI prec i@(I.Interval a b)
  | R.positive a = coshi
  | R.negative b = I.flip coshi
  | otherwise    = I.Interval R.one (R.max' (fromIntegral prec) R.Up ca cb)
  where
  coshi@(I.Interval ca cb) = I.monotone (\d -> M.cosh (R.roundDirMPFR d) prec) i

cosh' :: CMap R R
cosh' = withPrec (coshI . fromIntegral)

fact :: Word -> CMap g R
fact n = constant (\d p -> M.facw d p n)

-- TODO: implement tan
instance Floating (CMap g R) where
  sqrt = ap1 sqrt'
  pi = constant M.pi
  log = ap1 log'
  exp = ap1 exp'
  sin = ap1 sin'
  cos = ap1 cos'
  sinh = ap1 sinh'
  cosh = ap1 cosh'
  tanh = ap1 tanh'
  asin = ap1 asin'
  acos = ap1 acos'
  atan = ap1 atan'
  asinh = ap1 asinh'
  acosh = ap1 acosh'
  atanh = ap1 atanh'