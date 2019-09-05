{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances, IncoherentInstances #-}

module Diff where

import Prelude
import Control.Arrow
import Control.Applicative (liftA2)
import RealExpr (CMap (..))
import Data.Number.MPFR (MPFR)
import qualified Rounded as R
import Interval (Interval)
import qualified Expr as E

-- http://conal.net/blog/posts/higher-dimensional-higher-order-derivatives-functionally

type a :-* b = a -> b
data a :> b = D b (a :-* (a :> b))
type a :~> b = a -> (a :> b)

class VectorSpace v s | v -> s where
  zeroV   :: v              -- the zero vector
  (*^)    :: s -> v -> v    -- scale a vector
  (^+^)   :: v -> v -> v    -- add vectors
  negateV :: v -> v         -- additive inverse

class VectorSpace v s => InnerSpace v s | v -> s where
  (<.>) :: v -> v -> s

instance Num a => VectorSpace a a where
  zeroV = 0
  (*^) = (*)
  (^+^) = (+)
  negateV = negate

instance VectorSpace v s => VectorSpace (a->v) s where
  zeroV   = pure   zeroV
  (*^) s  = fmap   (s *^)
  (^+^)   = liftA2 (^+^)
  negateV = fmap   negateV

instance VectorSpace u s => VectorSpace (a :> u) (a :> s) where
  zeroV = D zeroV (\_ -> zeroV)
  D s s' *^ D x x' = D (s *^ x) (\d -> s' d *^ x' d)
  D a a' ^+^ D b b' = D (a ^+^ b) (\d -> a' d ^+^ b' d)
  negateV (D a a') = D (negateV a) (negateV a')

dConst :: VectorSpace b s => b -> a:>b
dConst b = b `D` const dZero

dZero :: VectorSpace b s => a:>b
dZero = dConst zeroV

dId :: VectorSpace u s => u :~> u
dId u = D u (\du -> dConst du)

linearD :: VectorSpace v s => (u :-* v) -> (u :~> v)
linearD f u = D (f u) (\du -> dConst (f du))

fstD :: VectorSpace a s => (a,b) :~> a
fstD = linearD fst

sndD :: VectorSpace b s => (a,b) :~> b
sndD = linearD snd

pairD :: g :~> a -> g :~> b -> g :~> (a, b)
pairD f g x = D (fx, gx) (pairD f'x g'x) where
  D fx f'x = f x
  D gx g'x = g x

dap1 :: a :~> b -> g :~> a -> g :~> b
dap1 f = (f @.)

dap2 :: (a, b) :~> c -> g :~> a -> g :~> b -> g :~> c
dap2 f x y = f @. pairD x y

square :: Num a => a :~> a
square x = dId x ^ 2

cube :: Num a => a :~> a
cube x = dId x ^ 3

-- Incorrect!
-- mult :: Num a => (a, a) :~> a
-- mult (x, y) = D (x * y) (\(dx, dy) ->

dMult :: Num a => g :~> a -> g :~> a -> g :~> a
dMult f g x = f x * g x

square' :: Num a => g :~> a -> g :~> a
square' x = dMult x x

cube' :: Num a => g :~> a -> g :~> a
cube' x = x^3 -- dMult x (square' x)

absD :: Num a => a :~> a
absD x = abs (dId x)

getValue :: a :> b -> b
getValue (D x dx) = x

getDeriv :: a :> b -> a :~> b
getDeriv (D x dx) = dx

getDerivTower :: Num a => a :> b -> [b]
getDerivTower (D x dx) = x : getDerivTower (dx 1)

instance Num b => Num (a->b) where
  fromInteger = pure . fromInteger
  (+)         = liftA2 (+)
  (*)         = liftA2 (*)
  negate      = fmap negate
  abs         = fmap abs
  signum      = fmap signum

instance (Num b, VectorSpace b b) => Num (a:>b) where
  fromInteger               = dConst . fromInteger
  D u0 u' + D v0 v'         = D (u0 + v0) (u' + v')
  D u0 u' - D v0 v'         = D (u0 - v0) (u' - v')
  u@(D u0 u') * v@(D v0 v') =
    D (u0 * v0) (\da -> (u * v' da) + (u' da * v))
  abs (D u u') = D (abs u) (\du -> dConst (signum u) * u' du)
  signum (D u u') = D (signum u) (error "no derivative for signum")

(>-<) :: VectorSpace u s =>
    (u -> u) -> ((a :> u) -> (a :> s)) -> (a :> u) -> (a :> u)
f >-< f' = \u@(D u0 u') -> D (f u0) (\da -> f' u *^ u' da)

-- absR :: R.Rounded a => CMap g (Interval a) :~> CMap g (Interval a)
-- absR = abs >-< signum

(@.) :: (b :~> c) -> (a :~> b) -> (a :~> c)
(f @. g) a0 = D c0 (c' @. b')
  where
    D b0 b' = g a0
    D c0 c' = f b0


exampleAbsDiff :: IO ()
exampleAbsDiff = E.runAndPrint $ E.asMPFR $ getDerivTower (absD 0) !! 1

example2 :: IO ()
example2 = E.runAndPrint $ E.asMPFR $ getDerivTower ((\x -> abs (x ^ 2)) dId 2) !! 2


-- I have no idea whether any of these are sensible
collapse1 :: CMap a (b -> c) -> CMap (a, b) c
collapse1 (CMap f) = CMap $ \(a, b) ->
  let (bc, f') = f a in
  (bc b, collapse1 f')

uncollapse1 :: CMap (a, b) c -> CMap a (b -> c)
uncollapse1 (CMap f) = CMap $ \a ->
  (\b -> let (c, f') = f (a, b) in c, let (_, f') = f (a, undefined) in uncollapse1 f')

collapse :: CMap a (CMap b c) -> CMap (a, b) c
collapse (CMap f) = CMap $ \(a, b) ->
  let (CMap g, f') = f a in
  let (c, g') = g b in
  (c, collapse f')

uncollapse :: CMap (a, b) c -> CMap a (CMap b c)
uncollapse f = CMap $ \a ->
  (g f a, uncollapse f)
  where
  g (CMap z) a = CMap $ \b -> let (c, z') = z (a, b) in (c, g z' a)