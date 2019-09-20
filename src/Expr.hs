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
  (!!)
) where

import Prelude hiding (max, min, pow, (&&), (||), (^), (<), (>))

import Control.Arrow (Arrow, arr, (<<<))
import Control.Category (Category)
import qualified Control.Category as C
import RealExpr (CMap, B)
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

-- Let statement with sharing
lett :: CMap g a -> (CMap (g, a) a -> CMap (g, a) b) -> CMap g b
lett x f = proc g -> do
  a <- x -< g
  f (arr snd) -< (g, a)

-- Weakening
wkn :: CMap g a -> CMap (g, x) a
wkn f = f <<< arr fst

instance Rounded a => Num (CMap g (Interval a)) where
  (+) = E.ap2 E.add
  (*) = E.ap2 E.mul
  negate = E.ap1 E.negate
  x - y = x + (-y)
  abs x = max x (-x)
  fromInteger = E.integer
  signum = E.ap1 E.signum

instance Rounded a => Fractional (CMap g (Interval a)) where
  fromRational = E.rational
  recip = E.ap1 E.recip
  (/) = E.ap2 E.div

-- use as a type hint
asMPFR :: CMap g (Interval MPFR) -> CMap g (Interval MPFR)
asMPFR = id

inEmptyCtx :: (forall g. CMap g a) -> CMap () a
inEmptyCtx x = x

runAndPrint :: Show a => CMap () a -> IO ()
runAndPrint = mapM_ (putStrLn . show) . E.runCMap

runAndPrint' :: Show a => Int -> CMap () a -> IO ()
runAndPrint' n = mapM_ (putStrLn . show) . take 10 . E.runCMap

sqrt2Example :: IO ()
sqrt2Example = runAndPrint $ asMPFR $ dedekind_cut (\x -> x < 0 || (x ^ 2) < 2)

quantificationExample :: IO ()
quantificationExample = runAndPrint $
  (exists_unit_interval (\x -> isTrue (x < asMPFR 0.5 && x > 0.3)))