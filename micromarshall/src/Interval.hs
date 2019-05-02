module Interval where

import Rounded (Rounded, Prec, RoundDir (Up, Down))
import qualified Rounded as R

data Interval a = Interval a a

lift :: a -> Interval a
lift x = Interval x x

realLine :: Rounded a => Interval a
realLine = Interval R.negativeInfinity R.positiveInfinity

iadd :: Rounded a => Prec -> Interval a -> Interval a -> Interval a
iadd p (Interval l1 u1) (Interval l2 u2) =
  Interval (R.add p Down l1 l2) (R.add p Up u1 u2)

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