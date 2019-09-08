module SelfContained.Compact where

import Prelude
import Control.Arrow (first)

import Data.Ratio
import Interval (Interval (..))
import qualified Interval as I

data Space cov cmpt = Space
  { done :: cov -> cmpt -> Bool }

cut_bisection :: (Ord a, Fractional a) => (a -> Ordering) -> Interval a -> Interval a
cut_bisection f (Interval a b) = let x = a / 2 + b / 2 in
  case f x of
    LT -> Interval x b
    EQ -> I.lift x
    GT -> Interval a x

maybe_cut_bisection :: (Ord a, Fractional a) => (a -> Maybe Ordering) -> Interval a -> Interval a
maybe_cut_bisection f i@(Interval a b) = let x = a / 2 + b / 2 in
  case f x of
    Nothing -> i
    Just cmp -> case cmp of
      LT -> Interval x b
      EQ -> Interval x x
      GT -> Interval a x

rat_sqrt :: Rational -> [Interval Rational]
rat_sqrt a = iterate (cut_bisection (\x -> compare (x^2) a))
  (if a > 1 then Interval (recip a) a else Interval a (recip a))

compare_int :: Ord a => a -> Interval a -> Maybe Ordering
compare_int x i = case compare x (I.lower i) of
  LT -> Just LT
  EQ -> if x == I.upper i then Just EQ else Nothing
  GT -> if x > I.upper i then Just GT else Nothing

r_sqrt :: Interval Rational -> [Interval Rational]
r_sqrt i = let ir = I.recip undefined i in
  iterate (maybe_cut_bisection (\x -> compare_int (x^2) i))
  (Interval (I.lower (I.min ir i)) (I.upper (I.max ir i)))

approx_compose :: [a] -> (a -> [b]) -> [b]
approx_compose xs f = go 0 xs where
  go i [] = []
  go i (y : ys) = f y !! i : go (i + 1) ys

rSpace :: Space Rational (Interval Rational)
rSpace = Space (\eps (Interval a b) -> b - a < eps)

runWith :: Space a b -> a -> [b] -> b
runWith (Space f) cover = g where
  g [] = error "No satisfying value"
  g (x : xs) = if f cover x then x else g xs

data R = R Rational Rational
  deriving (Eq, Show, Ord)
data Sierp = STrue | SUnknown
  deriving (Eq, Show, Ord)


dirac :: a -> [(a, Interval Rational)]
dirac x = [(x, I.lift 1)]

bernoulli :: Interval Rational -> [(Bool, Interval Rational)]
bernoulli p = [(True, p), (False, I.sub undefined (I.lift 1) p)]

probBind :: [(a, Interval Rational)] -> (a -> [(b, Interval Rational)]) -> [((a, b), Interval Rational)]
probBind xs f = do
  (x, px) <- xs
  (y, py) <- f x
  return ((x, y), I.mul undefined px py)

probMap :: (a -> b) -> [(a, Interval Rational)] -> [(b, Interval Rational)]
probMap f = map (first f)

uniformProb :: [[(Interval Rational, Interval Rational)]]
uniformProb = go 1 where
  go n = [ (( Interval (i % n) ((i + 1) % n)), I.lift (1 / fromIntegral n)) | i <- takeWhile (< n) [0..] ] : go (2 * n)

indepProd :: [(a, Interval Rational)] -> [(b, Interval Rational)] -> [((a, b), Interval Rational)]
indepProd xs ys = probBind xs (\_ -> ys)

showInterval :: (a -> String) -> Interval a -> String
showInterval s i = "(" ++ s (I.lower i) ++ " ... " ++ s (I.upper i) ++ ")"

endpoints :: Real a => Interval a -> (Double, Double)
endpoints i = (realToFrac (I.lower i), realToFrac (I.upper i))


sierpToBool :: Sierp -> Bool
sierpToBool STrue = True
sierpToBool SUnknown = False

boolToSierp :: Bool -> Sierp
boolToSierp True = STrue
boolToSierp False = SUnknown

gt0 :: R -> Sierp
gt0 (R l u) = if 0 < l then STrue else SUnknown

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