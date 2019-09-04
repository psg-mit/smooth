{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Diff where

import Control.Arrow
import RealExpr
import Data.Number.MPFR (MPFR)
import qualified Rounded as R
import Interval (Interval)
import Expr ()

-- http://conal.net/blog/posts/higher-dimensional-higher-order-derivatives-functionally
data DT a b = D b (Diff a b)
type Diff a b = a -> DT a b

class VectorSpace v s | v -> s where
  zeroV   :: CMap () v       -- the zero vector
  (*^)    :: CMap (s, v) v   -- scale a vector
  (^+^)   :: CMap (v, v) v   -- add vectors
  negateV :: CMap v v        -- additive inverse

instance VectorSpace (Interval MPFR) (Interval MPFR) where
  zeroV = 0
  (*^) = mul
  (^+^) = add
  negateV = RealExpr.negate

instance VectorSpace v s => VectorSpace (a->v) s where
  zeroV   = fmap const  zeroV
  -- (*^)  = proc (s, av) -> do
  --      <- (*^)
  --    returnA -< \a ->
  -- fmap   (s *^)
  -- (^+^)   = liftA2 (^+^)
  -- negateV = fmap   negateV

class VectorSpace v s => InnerSpace v s | v -> s where
  (<.>) :: CMap (v, v) s


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