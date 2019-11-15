{-|
A generic module for performing interval arithmetic using
the `Rounded` typeclass, which represents approximate
number types with operations that permit rounding up and down.
-}

module Interval where

import Prelude hiding (flip, recip)
import Rounded (Rounded, Prec, RoundDir (Up, Down))
import qualified Rounded as R
import Debug.Trace

data Interval a = Interval
  { lower :: a
  , upper :: a
  }

instance Rounded a => Show (Interval a) where
  show (Interval a b) = "[" ++ R.toString a ++ ", " ++ R.toString b ++ "]"

lift :: a -> Interval a
lift x = Interval x x

scalePos :: Rounded a => Prec -> a -> Interval a -> Interval a
scalePos p c (Interval a b) = Interval (R.mul p R.Down c a) (R.mul p R.Up c b)

realLine :: Rounded a => Interval a
realLine = Interval R.negativeInfinity R.positiveInfinity

unitInterval :: Rounded a => Interval a
unitInterval = Interval R.zero R.one

add :: Rounded a => Prec -> Interval a -> Interval a -> Interval a
add p (Interval l1 u1) (Interval l2 u2) =
  Interval (R.add p Down l1 l2) (R.add p Up u1 u2)

sub :: Rounded a => Prec -> Interval a -> Interval a -> Interval a
sub p (Interval l1 u1) (Interval l2 u2) =
  Interval (R.sub p Down l1 u2) (R.sub p Up u1 l2)

width :: Rounded a => Prec -> Interval a -> Interval a
width p (Interval l u) = sub p (lift u) (lift l)

mulpow2 :: Rounded a => Int -> Prec -> Interval a -> Interval a
mulpow2 i p = monotone (R.mulpow2 i p)

-- union and widen
union :: Rounded a => Interval a -> Interval a -> Interval a
union (Interval l1 u1) (Interval l2 u2) = -- trace ("union" ++ show (Interval l1 u1, Interval l2 u2)) $
  Interval (R.min l1 l2) (R.max u1 u2)

-- intersection: combine information from two sources
join :: Rounded a => Interval a -> Interval a -> Interval a
join (Interval l1 u1) (Interval l2 u2) =
  Interval (R.max l1 l2) (R.min u1 u2)

cmp :: Ord a => Interval a -> Interval a -> Maybe Ordering
cmp (Interval l1 u1) (Interval l2 u2)
  | u1 < l2   = Just LT
  | l1 > u2   = Just GT
  | otherwise = Nothing

recip :: Rounded a => Prec -> Interval a -> Interval a
recip p i@(Interval a b)
  | b < R.zero || R.zero < a = monotone (\d -> R.div p d R.one) (flip i)
  | otherwise  = realLine

div :: Rounded a => Prec -> Interval a -> Interval a -> Interval a
div p n d = mul p n (recip p d)

maybe_cut_bisection :: Rounded a => (a -> Maybe Ordering) -> Interval a -> Interval a
maybe_cut_bisection f i@(Interval a b) = let x = R.average a b in
  case f x of
    Nothing -> i
    Just cmp -> case cmp of
      LT -> Interval x b
      EQ -> undefined -- lift x
      GT -> Interval a x

negate :: Rounded a => Prec -> Interval a -> Interval a
negate p (Interval l u) = Interval (R.neg p Down u) (R.neg p Up l)

max :: Rounded a => Interval a -> Interval a -> Interval a
max (Interval l1 u1) (Interval l2 u2) =
  Interval (R.max l1 l2) (R.max u1 u2)

min :: Rounded a => Interval a -> Interval a -> Interval a
min (Interval l1 u1) (Interval l2 u2) =
    Interval (R.min l1 l2) (R.min u1 u2)

-- Kaucher multiplication
mul :: Rounded a => Prec -> Interval a -> Interval a -> Interval a
mul p (Interval a b) (Interval c d) = -- trace ("mul" ++ show (Interval a b, Interval c d, Interval l u))
  Interval l u
  where
  lmul = R.mul p Down
  l = if R.negative a then
          if R.negative b then
      if R.negative d then lmul b d else lmul a d
          else {- positive [b] -}
      if R.negative c then
        if R.negative d then lmul b c else R.min (lmul a d) (lmul b c)
      else {- positive [c] -}
        if R.negative d then R.zero else lmul a d
        else {- positive [a] -}
          if R.negative b then
      if R.negative c then
        if R.negative d then lmul b d else R.zero
      else {- positive [c] -}
        if R.negative d then R.max (lmul a c) (lmul b d) else lmul a c
          else {- positive [b] -}
      if R.negative c then lmul b c else lmul a c
  umul = R.mul p Up
  u = if R.negative a then
        if R.negative b then
    if R.negative c then umul a c else umul b c
        else {- positive [b] -}
    if R.negative c then
      if R.negative d then umul a c else R.max (umul a c) (umul b d)
    else {- positive [c] -}
      if R.negative d then R.zero else umul b d
      else {- positive [a] -}
        if R.negative b then
    if R.negative c then
      if R.negative d then umul a d else R.zero
    else {- positive [c] -}
      if R.negative d then R.min (umul a d) (umul b c) else umul b c
        else {- positive [b] -}
    if R.negative d then umul a d else umul b d

monotone :: Rounded a => (RoundDir -> a -> a) -> Interval a -> Interval a
monotone f (Interval a b) = Interval (f R.Down a) (f R.Up b)

rounded :: Rounded a => (RoundDir -> a) -> Interval a
rounded f = Interval (f R.Down) (f R.Up)

flip :: Interval a -> Interval a
flip (Interval a b) = Interval b a

pow :: Rounded a => Prec -> Interval a -> Int -> Interval a
pow prec i@(Interval a b) k
  | odd k     = monotonePow i
  | otherwise = i'
  where
  monotonePow = monotone (\d x -> R.pow prec d x k)
  lpow x = R.pow prec R.Down x k
  upow x = R.pow prec R.Up x k
  i'  = if R.negative a then
          if R.negative b then
            monotonePow (flip i)
          else {- non-negative [b] -}
            Interval R.zero (R.max (upow a) (upow b))
        else {- non-negative [a] -}
          if R.negative b then
            Interval (R.min (lpow a) (lpow b)) R.zero -- Marshall uses `max` here, I'm not sure why, seems potentially wrong
          else {- non-negative [b] -}
            monotonePow i