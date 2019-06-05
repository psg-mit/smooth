{-# LANGUAGE ExistentialQuantification, DataKinds, GADTs #-}
{-# LANGUAGE PolyKinds, TypeOperators, RankNTypes, LiberalTypeSynonyms #-}

module Expr where
import Lib

data Ty =
  forall a. K a
  | forall a b. a :-> b
  | forall a b. a :* b
  | forall a b. a :+ b

-- data Expr' f (a :: (* -> * -> *) -> * -> *) where
--   Var :: f a -> Expr' f a
--   App :: Expr' f (a :->: b) -> Expr' f a -> Expr' f b
--   Abs :: (Expr' f a -> Expr' f b) -> Expr' f (a :->: b)

-- type Rep a k g = g `k` a

-- type (a :*: b) k g = (a k g, b k g)
-- type (a :+: b) k g = Either (a k g) (b k g)
-- type (a :->: b) k g = forall d. Extends k g d => a k d -> b k d

-- compile :: (forall f. Expr' f a) -> a k g
-- compile (Var x) = x
-- compile (App f x) = (compile f) (compile x)
-- compile (Abs f) = compile (f (Var 0))