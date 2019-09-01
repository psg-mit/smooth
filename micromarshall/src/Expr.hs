{-# LANGUAGE FlexibleInstances #-}

module Expr (
  module Expr,
  Interval,
  MPFR
) where

import Prelude hiding (max, min)

import RealExpr
import Interval (Interval (..))
import Rounded (Rounded)
import Data.Number.MPFR (MPFR)

type K = RFunc ()

max :: Rounded a => RFunc g (Interval a) -> RFunc g (Interval a) -> RFunc g (Interval a)
max = ap2 emax

instance Rounded a => Num (RFunc g (Interval a)) where
  (+) = ap2 eplus
  (*) = ap2 emul
  negate = ap1 enegate
  x - y = x + (-y)
  abs x = max x (-x)
  fromInteger = econstD . fromInteger

runAndPrint :: Show a => RFunc () a -> IO ()
runAndPrint = mapM_ (putStrLn . show) . runRFunc