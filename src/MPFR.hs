module MPFR where

import Prelude (Word, ($), fromIntegral)
import qualified Interval as I
import Interval (Interval)
import RealExpr
import qualified Rounded as R
import qualified Data.Number.MPFR as M

type R = Interval M.MPFR

monotone :: (M.RoundMode -> M.Precision -> M.MPFR -> M.MPFR) -> CMap R R
monotone f = withPrec $ \p -> I.monotone (\d x -> f (R.roundDirMPFR d) (fromIntegral p) x)

constant :: (M.RoundMode -> M.Precision -> M.MPFR) -> CMap g R
constant f = withPrec $ \p _ -> I.rounded (\d -> f (R.roundDirMPFR d) (fromIntegral p))

exp' :: CMap R R
exp' = monotone M.exp

exp :: CMap g R -> CMap g R
exp = ap1 exp'

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

log :: CMap g R -> CMap g R
log = ap1 log'

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

sqrt :: CMap g R -> CMap g R
sqrt = ap1 MPFR.sqrt'


-- Constants
pi :: CMap g R
pi = constant M.pi

log2c :: CMap g R
log2c = constant M.log2c

euler :: CMap g R
euler = constant M.euler

catalan :: CMap g R
catalan = constant M.catalan


fact :: Word -> CMap g R
fact n = constant (\d p -> M.facw d p n)