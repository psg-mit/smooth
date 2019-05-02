module Rounded where

import Data.Number.MPFR (MPFR)
import qualified Data.Number.MPFR as M

data RoundDir = Up | Down

anti :: RoundDir -> RoundDir
anti Up = Down
anti Down = Up

type Prec = Word

class Rounded a where
  ofInt :: Prec -> RoundDir -> Int -> a
  zero :: a
  one :: a
  negativeOne :: a
  two :: a
  half :: Prec -> RoundDir -> a
  cmp :: a -> a -> Ordering
  min :: a -> a -> a
  max :: a -> a -> a
  lt :: a -> a -> Bool
  gt :: a -> a -> Bool
  eq :: a -> a -> Bool
  leq :: a -> a -> Bool
  geq :: a -> a -> Bool
  isZero :: a -> Bool
  positive :: a -> Bool
  negative :: a -> Bool
  positiveInfinity :: a
  negativeInfinity :: a
  isInfinity :: a -> Bool
  isPositiveInfinity :: a -> Bool
  isNegativeInfinity :: a -> Bool
  toString :: a -> String
  ofString :: Prec -> RoundDir -> String -> a
  average :: a -> a -> a
  add :: Prec -> RoundDir -> a -> a -> a
  sub :: Prec -> RoundDir -> a -> a -> a
  neg :: Prec -> RoundDir -> a -> a
  mul :: Prec -> RoundDir -> a -> a -> a
  div :: Prec -> RoundDir -> a -> a -> a

roundDirMPFR :: RoundDir -> M.RoundMode
roundDirMPFR Up = M.Up
roundDirMPFR Down = M.Down

instance Rounded MPFR where
  add p d = M.add (roundDirMPFR d) (fromIntegral p)
  negativeInfinity = M.setInf 0 (-1)
  positiveInfinity = M.setInf 0 1