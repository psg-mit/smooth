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

instance Rounded MPFR where
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
  max a b = case M.cmp a b of
    Just GT -> a
    Just _ -> b
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