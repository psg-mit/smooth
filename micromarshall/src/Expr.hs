{-# LANGUAGE FlexibleInstances #-}

module Expr (
  module Expr,
  Interval,
  MPFR,
  ($)
) where

import Prelude hiding (max, min, pow, (&&), (||), (^), (<), (>))

import Control.Arrow (arr)
import RealExpr
import Interval (Interval (..), unitInterval)
import Rounded (Rounded)
import qualified Rounded as R
import Data.Number.MPFR (MPFR)

type K = RFunc ()

max :: Rounded a => RFunc g (Interval a) -> RFunc g (Interval a) -> RFunc g (Interval a)
max = ap2 emax

infixr 3 &&
(&&) :: RFunc g B -> RFunc g B -> RFunc g B
(&&) = ap2 eand

infixr 2 ||
(||) :: RFunc g B -> RFunc g B -> RFunc g B
(||) = ap2 eor

infix 4 <
(<) :: Rounded a => RFunc g (Interval a) -> RFunc g (Interval a) -> RFunc g B
(<) = ap2 elt

infix 4 >
(>) :: Rounded a => RFunc g (Interval a) -> RFunc g (Interval a) -> RFunc g B
x > y = y < x

infixr 8 ^
(^) :: Rounded a => RFunc g (Interval a) -> Int -> RFunc g (Interval a)
x ^ k = ap1 (epow k) x

isTrue :: RFunc g B -> RFunc g Bool
isTrue = ap1 (arr fst)

isFalse :: RFunc g B -> RFunc g Bool
isFalse = ap1 (arr snd)

dedekind_cut :: Rounded a => (RFunc (g, Interval a) (Interval a) -> RFunc (g, Interval a) B)
             -> RFunc g (Interval a)
dedekind_cut f = secondOrderPrim dedekind_cut' (f (arr snd))

integral_unit_interval :: (Show a, Rounded a) => (RFunc (g, Interval a) (Interval a) -> RFunc (g, Interval a) (Interval a))
             -> RFunc g (Interval a)
integral_unit_interval f = secondOrderPrim (integral' 16 unitInterval) (f (arr snd))

forall_unit_interval :: (Show a, Rounded a) => (RFunc (g, Interval a) (Interval a) -> RFunc (g, Interval a) Bool)
             -> RFunc g Bool
forall_unit_interval f = secondOrderPrim (forall_interval' 16 unitInterval) (f (arr snd))

exists_unit_interval :: (Show a, Rounded a) => (RFunc (g, Interval a) (Interval a) -> RFunc (g, Interval a) Bool)
             -> RFunc g Bool
exists_unit_interval f = secondOrderPrim (exists_interval' 16 unitInterval) (f (arr snd))

instance Rounded a => Num (RFunc g (Interval a)) where
  (+) = ap2 eplus
  (*) = ap2 emul
  negate = ap1 enegate
  x - y = x + (-y)
  abs x = max x (-x)
  fromInteger = econstD . fromInteger

instance Rounded a => Fractional (RFunc g (Interval a)) where
  fromRational = econstD . fromRational

runAndPrint :: Show a => RFunc () a -> IO ()
runAndPrint = mapM_ (putStrLn . show) . runRFunc

sqrt2Example :: IO ()
sqrt2Example = runAndPrint $ (dedekind_cut (\x -> x < 0 || (x ^ 2) < 2) :: K (Interval MPFR))

quantificationExample :: IO ()
quantificationExample = runAndPrint $
  (exists_unit_interval (\x -> isTrue (x < constMPFR 0.5 && x > 0.3)))