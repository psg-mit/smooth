{-# LANGUAGE ExistentialQuantification #-}

module OpSem where

import Control.Arrow (first)

import Data.List (intercalate)
import Data.Ratio
import Data.Set (Set)
import qualified Data.Set as S
import Numeric.Interval
import qualified Numeric.Interval as Int

cut_bisection :: (Ord a, Fractional a) => (a -> Ordering) -> Interval a -> Interval a
cut_bisection f i = let x = midpoint i in
  case f x of
    LT -> (x ... sup i)
    EQ -> Int.singleton x
    GT -> (inf i ... x)

maybe_cut_bisection :: (Ord a, Fractional a) => (a -> Maybe Ordering) -> Interval a -> Interval a
maybe_cut_bisection f i = let x = midpoint i in
  case f x of
    Nothing -> i
    Just cmp -> case cmp of
      LT -> (x ... sup i)
      EQ -> Int.singleton x
      GT -> (inf i ... x)

rat_sqrt :: Rational -> [Interval Rational]
rat_sqrt a = iterate (cut_bisection (\x -> compare (x^2) a))
  (if a > 1 then (recip a ... a) else (a ... recip a))

compare_int :: Ord a => a -> Interval a -> Maybe Ordering
compare_int x i = case compare x (inf i) of
  LT -> Just LT
  EQ -> if x == sup i then Just EQ else Nothing
  GT -> if x > sup i then Just GT else Nothing

r_sqrt :: Interval Rational -> [Interval Rational]
r_sqrt i = let ir = recip i in
  iterate (maybe_cut_bisection (\x -> compare_int (x^2) i))
  (inf (min ir i) ... sup (max ir i))

approx_compose :: [a] -> (a -> [b]) -> [b]
approx_compose xs f = go 0 xs where
  go i [] = []
  go i (y : ys) = f y !! i : go (i + 1) ys

data R = R LowerR UpperR
  deriving (Eq, Show, Ord)

data LowerR = NegInf | LR Rational
  deriving (Eq, Show, Ord)

data UpperR = UR Rational | PosInf
  deriving (Eq, Show, Ord)

instance Num LowerR where
  LR x + LR y = LR (x + y)
  NegInf + _ = NegInf
  _ + NegInf = NegInf

instance Num UpperR where
  UR x + UR y = UR (x + y)
  PosInf + _ = PosInf
  _ + PosInf = PosInf

bound :: Int -> Rational -> (R -> (Bool, Bool)) -> (Int, R)
bound 0  _ _ = (0, R NegInf PosInf)
bound p' b f = let p = p' - 1 in
  if fst (f (fromRat (-b))) && snd (f (fromRat b))
    then (p, R (LR (-b)) (UR b))
    else bound p (2 * b) f

trisect :: (Int, R) -> (R -> (Bool, Bool)) -> R
trisect (0, i) _ = i
trisect (p', R (LR l) (UR u)) f = trisect (p, R (LR l') (UR u')) f
  where
  p = p' - 1
  a = (2/3) * l + (1/3) * u
  b = (1/3) * l + (2/3) * u
  l' = if fst (f (fromRat a)) then a else l
  u' = if snd (f (fromRat b)) then b else u
trisect (p, _) _ = error "should not happen"

dedekind_cut :: (R -> (Bool, Bool)) -> Int -> R
dedekind_cut f p = trisect (bound p 1 f) f

showInterval :: (a -> String) -> Interval a -> String
showInterval s i = "(" ++ s (inf i) ++ " ... " ++ s (sup i) ++ ")"

endpoints :: Real a => Interval a -> (Double, Double)
endpoints i = (realToFrac (inf i), realToFrac (sup i))

plus :: R -> R -> R
plus (R l u) (R l' u') = R (l + l') (u + u')

fromRat :: Rational -> R
fromRat x = R (LR x) (UR x)

approx_eps :: Rational -> R -> Bool
approx_eps eps (R (LR l) (UR u)) = u - l < eps
approx_eps eps (R _ _) = False

rlt :: R -> R -> Bool
rlt (R _ (UR ux)) (R (LR ly) _) = ux < ly
rlt (R _ PosInf) _ = False
rlt _ (R NegInf _) = False

rltb :: R -> R -> (Bool, Bool)
rltb x y = (rlt x y, rlt y x)

orb :: (Bool, Bool) -> (Bool, Bool) -> (Bool, Bool)
orb (p1, q1) (p2, q2) = (p1 || p2, q1 && q2)

andb :: (Bool, Bool) -> (Bool, Bool) -> (Bool, Bool)
andb (p1, q1) (p2, q2) = (p1 && p2, q1 || q2)

square :: R -> R
square (R NegInf _) = R (LR 0) PosInf
square (R _ PosInf) = R (LR 0) PosInf
square (R (LR l) (UR u)) = R (LR lower) (UR maxsq)
  where
  lower = if l < 0 && 0 < u then 0 else minsq
  maxsq = max sql squ
  minsq = min sql squ
  sql = l^2
  squ = u^2

sqrt :: R -> Int -> R
sqrt x = dedekind_cut (\q -> orb (rltb q (fromRat 0)) (rltb (square q) x))

toStream :: (Int -> a) -> [a]
toStream = go 0 where
  go n f = f n : go (n + 1) f

rattex :: Rational -> String
rattex q = let (n, d) = (numerator q, denominator q) in
  if d == 1
    then show n
    else show n ++ "/" ++ show d
  --"\\frac{" ++ show (numerator q) ++ "}{" ++ show (denominator q) ++ "}"

lrtex :: LowerR -> String
lrtex NegInf = "-\\infty"
lrtex (LR l) = rattex l

urtex :: UpperR -> String
urtex PosInf = "\\infty"
urtex (UR u) = rattex u

pairtex :: (a -> String) -> (b -> String) -> (a, b) -> String
pairtex pl pr (l, r) = "(" ++ pl l ++ ", " ++ pr r ++ ")"

rtex :: R -> String
rtex (R l u) = "$" ++ pairtex lrtex urtex (l, u) ++ "$"

proptex :: Bool -> String
proptex True = "\\texttt{True}"
proptex False = "\\texttt{Unknown}"

booltex :: (Bool, Bool) -> String
booltex = pairtex proptex proptex

latexTable :: [[String]] -> String
latexTable = intercalate "\n" . map (intercalate " & ")

outputTable :: [Result] -> String
outputTable es = latexTable (map out [0..8]) where
  out p = ("\\\\ " ++ show p) : map (\(Result e) -> toTex (e p)) es

mycomp :: Int -> R
mycomp = do
  y <- OpSem.sqrt (fromRat 2)
  return (y `plus` fromRat 1)

class TeX a where
  toTex :: a -> String

instance TeX R where
  toTex = rtex

instance TeX Bool where
  toTex = proptex

instance (TeX a, TeX b) => TeX (a, b) where
  toTex = pairtex toTex toTex

data Result = forall a. TeX a => Result (Int -> a)

example1 :: String
example1 = outputTable (map Result [const two, sqrt2, const one, sqrt2plus1]) where
  two = fromRat 2
  one = fromRat 1
  sqrt2 = OpSem.sqrt two
  sqrt2plus1 = fmap (plus one) sqrt2

example2 :: String
example2 = outputTable [Result sqrt2, Result sqrt2gt1, Result sqrt2lt3, Result conj] where
  sqrt2 = OpSem.sqrt (fromRat 2)
  sqrt2gt1 = rltb (fromRat 1) <$> sqrt2
  sqrt2lt3 = rltb <$> sqrt2 <*> pure (fromRat 3)
  conj = andb <$> sqrt2gt1 <*> sqrt2lt3

test :: [R]
test = toStream mycomp