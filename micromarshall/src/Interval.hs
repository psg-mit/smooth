{-# LANGUAGE FlexibleInstances #-}

module Interval where

import Rounded (Rounded, Prec, RoundDir (Up, Down))
import qualified Rounded as R

data Interval a = Interval a a

instance Rounded a => Show (Interval a) where
  show (Interval a b) = "[" ++ R.toString a ++ ", " ++ R.toString b ++ "]"

lift :: a -> Interval a
lift x = Interval x x

realLine :: Rounded a => Interval a
realLine = Interval R.negativeInfinity R.positiveInfinity

iadd :: Rounded a => Prec -> Interval a -> Interval a -> Interval a
iadd p (Interval l1 u1) (Interval l2 u2) =
  Interval (R.add p Down l1 l2) (R.add p Up u1 u2)

-- union and widen
iunion :: Rounded a => Interval a -> Interval a -> Interval a
iunion (Interval l1 u1) (Interval l2 u2) =
  Interval (R.min l1 l2) (R.max u1 u2)

icmp :: Ord a => Interval a -> Interval a -> Maybe Ordering
icmp (Interval l1 u1) (Interval l2 u2) = case compare u1 l2 of
  LT -> Just LT
  _ -> case compare l1 u2 of
    GT -> Just GT
    _ -> Nothing

irecip :: Rounded a => Prec -> Interval a -> Interval a
irecip p (Interval a b) = case compare R.zero a of
  LT -> Interval (R.div p R.Down R.one a) (R.div p R.Up R.one b)
  _ -> case compare b R.zero of
    LT -> Interval (R.div p R.Down R.one b) (R.div p R.Up R.one a)
    _ -> realLine

maybe_cut_bisection :: Rounded a => (a -> Maybe Ordering) -> Interval a -> Interval a
maybe_cut_bisection f i@(Interval a b) = let x = R.average a b in
  case f x of
    Nothing -> i
    Just cmp -> case cmp of
      LT -> Interval x b
      EQ -> undefined -- lift x
      GT -> Interval a x

inegate :: Rounded a => Prec -> Interval a -> Interval a
inegate p (Interval l u) = Interval (R.neg p Down u) (R.neg p Up l)

imax :: Rounded a => Interval a -> Interval a -> Interval a
imax (Interval l1 u1) (Interval l2 u2) =
  Interval (R.max l1 l2) (R.max u1 u2)

imin :: Rounded a => Interval a -> Interval a -> Interval a
imin (Interval l1 u1) (Interval l2 u2) =
    Interval (R.min l1 l2) (R.min u1 u2)

-- Kaucher multiplication
imul :: Rounded a => Prec -> Interval a -> Interval a -> Interval a
imul p (Interval a b) (Interval c d) = Interval l u
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

imonotone :: Rounded a => (RoundDir -> a -> a) -> Interval a -> Interval a
imonotone f (Interval a b) = Interval (f R.Down a) (f R.Up b)

pow :: Rounded a => Prec -> Interval a -> Int -> Interval a
pow prec i@(Interval a b) k =
  if even k
    then let lpow = R.pow prec R.Down in
    Interval
    (if R.negative a then
    if R.negative b then
      lpow b k
    else {- non-negative [b] -}
      R.zero
  else {- non-negative [a] -}
    if R.negative b then
      R.max (lpow a k) (lpow b k)
    else {- non-negative [b] -}
      lpow a k)
   (
      let upow = R.pow prec R.Up in
  if R.negative a then
    if R.negative b then
      upow a k
    else {- non-negative [b] -}
      R.max (upow a k) (upow b k)
  else {- non-negative [a] -}
    if R.negative b then
      R.zero
    else {- non-negative [b] -}
      upow b k
    )
    else imonotone (\d x -> R.pow prec d x k) i