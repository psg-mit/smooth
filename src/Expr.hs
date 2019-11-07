{-|
Lift the first-order language for continuous maps `CMap`
into a higher-order language in Haskell by simply
using generalized points `CMap g a` at "stage of definition" `g`.

For instance, `add : CMap (R, R) R` becomes
`(+) : forall g. CMap g R -> CMap g R -> CMap g R`
which is "equivalent".
-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE RankNTypes #-}

module Expr (
  module Expr,
  Interval,
  MPFR,
  ($),
  Num ((+), (*), (-), abs, negate),
  Fractional (..),
  (!!),
) where

import Prelude hiding (max, min, pow, (&&), (||), (^), (<), (>))

import Control.Arrow (Arrow, arr, (<<<))
import Control.Category (Category)
import qualified Control.Category as C
import RealExpr (CMap, B, CNum (..), CFractional (..), CFloating (..), ap1, ap2)
import qualified RealExpr as E
import Interval (Interval (..), unitInterval)
import Rounded (Rounded)
import qualified Rounded as R
import Data.Number.MPFR (MPFR)

type K = CMap ()

max :: Rounded a => CMap g (Interval a) -> CMap g (Interval a) -> CMap g (Interval a)
max = E.ap2 E.max

infixr 3 &&
(&&) :: CMap g B -> CMap g B -> CMap g B
(&&) = E.ap2 E.and

infixr 2 ||
(||) :: CMap g B -> CMap g B -> CMap g B
(||) = E.ap2 E.or

infix 4 <
(<) :: Rounded a => CMap g (Interval a) -> CMap g (Interval a) -> CMap g B
(<) = E.ap2 E.lt

infix 4 >
(>) :: Rounded a => CMap g (Interval a) -> CMap g (Interval a) -> CMap g B
x > y = y < x

infixr 8 ^
(^) :: Rounded a => CMap g (Interval a) -> Int -> CMap g (Interval a)
x ^ k = E.ap1 (E.pow k) x

isTrue :: CMap g B -> CMap g Bool
isTrue = E.ap1 (arr fst)

isFalse :: CMap g B -> CMap g Bool
isFalse = E.ap1 (arr snd)

mkInterval :: Rounded a => CMap g (Interval a) -> CMap g (Interval a) -> CMap g (Interval a)
mkInterval = E.ap2 E.mkInterval

dedekind_cut :: Rounded a => (CMap (g, Interval a) (Interval a) -> CMap (g, Interval a) B)
             -> CMap g (Interval a)
dedekind_cut f = E.secondOrderPrim E.dedekind_cut' (f (arr snd))

integral_unit_interval :: Rounded a => (CMap (g, Interval a) (Interval a) -> CMap (g, Interval a) (Interval a))
             -> CMap g (Interval a)
integral_unit_interval f = E.secondOrderPrim (E.integral' 16 unitInterval) (f (arr snd))

forall_unit_interval :: (Show a, Rounded a) => (CMap (g, Interval a) (Interval a) -> CMap (g, Interval a) Bool)
             -> CMap g Bool
forall_unit_interval f = E.secondOrderPrim (E.forall_interval' 16 unitInterval) (f (arr snd))

exists_unit_interval :: (Show a, Rounded a) => (CMap (g, Interval a) (Interval a) -> CMap (g, Interval a) Bool)
             -> CMap g Bool
exists_unit_interval f = E.secondOrderPrim (E.exists_interval' 16 unitInterval) (f (arr snd))

restrictReal :: Rounded a => CMap g Bool -> CMap g (Interval a) -> CMap g (Interval a)
restrictReal = E.ap2 E.restrictReal

-- Let statement with sharing
lett :: CMap g a -> (CMap (g, a) a -> CMap (g, a) b) -> CMap g b
lett x f = proc g -> do
  a <- x -< g
  f (arr snd) -< (g, a)

-- Weakening
wkn :: CMap g a -> CMap (g, x) a
wkn f = f <<< arr fst

instance CNum a => Num (CMap g a) where
  (+) = ap2 cadd
  (-) = ap2 csub
  (*) = ap2 cmul
  negate = ap1 cnegate
  abs = ap1 cabs
  signum = ap1 csignum
  fromInteger = cfromInteger

instance CFractional a => Fractional (CMap g a) where
  (/) = ap2 cdiv
  recip = ap1 crecip
  fromRational = cfromRational


instance CFloating a => Floating (CMap g a) where
  pi = cpi
  exp = ap1 cexp
  log = ap1 clog
  sqrt = ap1 csqrt
  sin = ap1 csin
  cos = ap1 ccos
  tan = ap1 ctan
  asin = ap1 casin
  acos = ap1 cacos
  atan = ap1 catan
  sinh = ap1 csinh
  cosh = ap1 ccosh
  tanh = ap1 ctanh
  asinh = ap1 casinh
  acosh = ap1 cacosh
  atanh = ap1 catanh
  -- log1p = ap1 clog1p
  -- expm1 = ap1 cexpm1
  -- log1pexp = ap1 clog1pexp
  -- log1mexp = ap1 clog1mexp

-- use as a type hint
asMPFR :: CMap g (Interval MPFR) -> CMap g (Interval MPFR)
asMPFR = id

inEmptyCtx :: CMap () a -> CMap () a
inEmptyCtx = id

runAndPrint :: Show a => CMap () a -> IO ()
runAndPrint = mapM_ (putStrLn . show) . E.runCMap

runAndPrint' :: Show a => Int -> CMap () a -> IO ()
runAndPrint' n = mapM_ (putStrLn . show) . take 10 . E.runCMap

-- sqrt2Example :: IO ()
-- sqrt2Example = runAndPrint $ asMPFR $ dedekind_cut (\x -> x < 0 || (x ^ 2) < 2)

-- quantificationExample :: IO ()
-- quantificationExample = runAndPrint $
--   (exists_unit_interval (\x -> isTrue (x < asMPFR 0.5 && x > 0.3)))