{-|
A typeclass for multi-precision arithmetic,
so that we can implement the fundamental arithmetic
operations without explicitly tying ourselves to MPFR.
-}

module Rounded where

import Data.Ratio (Ratio)
import Prelude
import Data.Number.MPFR (MPFR)
import qualified Data.Number.MPFR as M

data RoundDir = Up | Down

anti :: RoundDir -> RoundDir
anti Up = Down
anti Down = Up

type Prec = Word

class Ord a => Rounded a where
  ofInteger :: Prec -> RoundDir -> Integer -> a
  zero :: a
  one :: a
  negativeOne :: a
  min :: a -> a -> a
  max :: a -> a -> a
  min' :: Prec -> RoundDir -> a -> a -> a
  max' :: Prec -> RoundDir -> a -> a -> a
  isZero :: a -> Bool
  positive :: a -> Bool
  positive = (> zero)
  negative :: a -> Bool
  negative = (< zero)
  positiveInfinity :: a
  negativeInfinity :: a
  isInfinity :: a -> Bool
  isPositiveInfinity :: a -> Bool
  isPositiveInfinity x = isInfinity x && positive x
  isNegativeInfinity :: a -> Bool
  isNegativeInfinity x = isInfinity x && negative x
  toString :: a -> String
  ofString :: Prec -> RoundDir -> String -> a
  average :: a -> a -> a
  add :: Prec -> RoundDir -> a -> a -> a
  sub :: Prec -> RoundDir -> a -> a -> a
  neg :: Prec -> RoundDir -> a -> a
  mul :: Prec -> RoundDir -> a -> a -> a
  div :: Prec -> RoundDir -> a -> a -> a
  pow :: Prec -> RoundDir -> a -> Int -> a
  mulpow2 :: Int -> Prec -> RoundDir -> a -> a

roundDirMPFR :: RoundDir -> M.RoundMode
roundDirMPFR Up = M.Up
roundDirMPFR Down = M.Down

instance (Integral a, Read a, Show a) => Rounded (Ratio a) where
  add p d = (+)
  sub p d = (-)
  mul p d = (*)
  div p d = (/)
  pow p d x k = x ^ k
  negativeInfinity = error "negative infinity"
  positiveInfinity = error "positive infinity"
  zero = 0
  one = 1
  min = Prelude.min
  max = Prelude.max
  min' p d = Prelude.min
  max' p d = Prelude.max
  neg p d = negate
  average a b = a / 2 + b / 2
  mulpow2 i p d x = (2^i) * x
  ofInteger p d = fromIntegral
  negativeOne = - 1
  isInfinity = const False
  isZero = (==) 0
  ofString p d = read
  toString = show