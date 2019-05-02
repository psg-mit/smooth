module Compact where

import Control.Arrow (first)

import Data.Ratio
import Data.Set (Set)
import qualified Data.Set as S
import Numeric.Interval
import qualified Numeric.Interval as Int

data Space cov cmpt = Space
  { done :: cov -> cmpt -> Bool }

sret :: a -> Set a
sret = S.singleton

sbind :: Ord b => Set a -> (a -> Set b) -> Set b
sbind s f = S.unions [ f x | x <- S.toList s]

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

rSpace :: Space Rational (Interval Rational)
rSpace = Space (\eps int -> width int < eps)

runWith :: Space a b -> a -> [b] -> b
runWith (Space f) cover = g where
  g [] = error "No satisfying value"
  g (x : xs) = if f cover x then x else g xs

data R = R Rational Rational
  deriving (Eq, Show, Ord)
data Sierp = STrue | SFalse
  deriving (Eq, Show, Ord)


dirac :: a -> [(a, Interval Rational)]
dirac x = [(x, Int.singleton 1)]

bernoulli :: Interval Rational -> [(Bool, Interval Rational)]
bernoulli p = [(True, p), (False, 1 - p)]

probBind :: [(a, Interval Rational)] -> (a -> [(b, Interval Rational)]) -> [((a, b), Interval Rational)]
probBind xs f = do
  (x, px) <- xs
  (y, py) <- f x
  return ((x, y), px * py)

probMap :: (a -> b) -> [(a, Interval Rational)] -> [(b, Interval Rational)]
probMap f = map (first f)

uniformProb :: [[(Interval Rational, Interval Rational)]]
uniformProb = go 1 where
  go n = [ (( i % n ... (i + 1) % n), Int.singleton (1 / fromIntegral n)) | i <- takeWhile (< n) [0..] ] : go (2 * n)

indepProd :: [(a, Interval Rational)] -> [(b, Interval Rational)] -> [((a, b), Interval Rational)]
indepProd xs ys = probBind xs (\_ -> ys)

showInterval :: (a -> String) -> Interval a -> String
showInterval s i = "(" ++ s (inf i) ++ " ... " ++ s (sup i) ++ ")"

endpoints :: Real a => Interval a -> (Double, Double)
endpoints i = (realToFrac (inf i), realToFrac (sup i))


sierpToBool :: Sierp -> Bool
sierpToBool STrue = True
sierpToBool SFalse = False

boolToSierp :: Bool -> Sierp
boolToSierp True = STrue
boolToSierp False = SFalse

gt0 :: R -> S.Set Sierp
gt0 (R l u) = S.fromList [ STrue | 0 < u && l <= u ]
            `S.union` S.fromList [ SFalse | l <= 0 && l <= u ]

plus :: R -> R -> R
plus (R l u) (R l' u') = R (l + l') (u + u')

fromRat :: Rational -> R
fromRat x = R x x

approx_eps :: Rational -> R -> Bool
approx_eps eps (R l u) = u - l < eps

approx_Sierp :: Bool -> Bool
approx_Sierp = id

test :: (Double, Double)
test = endpoints $ runWith rSpace 1e-2 $ approx_compose (rat_sqrt 2) r_sqrt