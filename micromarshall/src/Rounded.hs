module Rounded where

import Data.Number.MPFR (MPFR)
import qualified Data.Number.MPFR as M

data RoundDir = Up | Down

anti :: RoundDir -> RoundDir
anti Up = Down
anti Down = Up

type Prec = Word

class Ord a => Rounded a where
  ofInt :: Prec -> RoundDir -> Int -> a
  zero :: a
  one :: a
  negativeOne :: a
  two :: a
  half :: Prec -> RoundDir -> a
  min :: a -> a -> a
  max :: a -> a -> a
  min' :: Prec -> RoundDir -> a -> a -> a
  max' :: Prec -> RoundDir -> a -> a -> a
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
  pow :: Prec -> RoundDir -> a -> Int -> a
  -- `fromDouble` is just for convenience for now
  fromDouble :: Prec -> RoundDir -> Double -> a

roundDirMPFR :: RoundDir -> M.RoundMode
roundDirMPFR Up = M.Up
roundDirMPFR Down = M.Down

instance Rounded MPFR where
  add p d = M.add (roundDirMPFR d) (fromIntegral p)
  mul p d = M.mul (roundDirMPFR d) (fromIntegral p)
  div p d = M.div (roundDirMPFR d) (fromIntegral p)
  pow p d x k = M.powi (roundDirMPFR d) (fromIntegral p) x k
  negativeInfinity = M.setInf 0 (-1)
  positiveInfinity = M.setInf 0 1
  fromDouble p d = M.fromDouble (roundDirMPFR d) (fromIntegral p)
  zero = M.zero
  one = M.one
  negative = M.greater M.zero
  positive = M.less M.zero
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