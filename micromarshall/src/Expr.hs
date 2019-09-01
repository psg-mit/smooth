{-# LANGUAGE ExistentialQuantification, DataKinds, GADTs #-}
{-# LANGUAGE PolyKinds, TypeOperators, RankNTypes, LiberalTypeSynonyms #-}
{-# LANGUAGE TypeInType, TypeFamilies, MultiParamTypeClasses, FlexibleInstances #-}

module Expr where
import Data.Kind (type (*))
--import Lib

data Ty =
  forall a. K a
  | Unit
  | forall a b. a :-> b
  | forall a b. a :* b
  | forall a b. a :+ b

class Cartesian (c :: Ty -> Ty -> *) where
  unit :: c g Unit
  compose :: c g a -> c a b -> c g b
  fst' :: c (a :* b) a
  snd' :: c (a :* b) b
  id' :: c a a

class Cartesian c => CCC c where
  abstract :: c (g :* a) b -> c g (a :-> b)
  appl :: c g (a :-> b) -> c g a -> c g b

data Expr (c :: Ty -> Ty -> *) :: Ty -> * where
  Const :: c 'Unit a -> Expr c a
  App :: Expr c (a ':-> b) -> Expr c a -> Expr c b
  Abs :: (Expr c a -> Expr c b) -> Expr c (a ':-> b)

data InList :: Ty -> [Ty] -> * where
  InHere :: InList x (x : xs)
  InThere :: InList x ys -> InList x (y : ys)

class HasProj c g a where
  proj :: c g a

instance CCC c => HasProj c a a where
  proj = id'

instance (CCC c, HasProj c g a) => HasProj c (g :* b) a where
  proj = fst' `compose` proj

data Expr' (c :: Ty -> Ty -> *) :: Ty -> Ty -> * where
  Const' :: c g a -> Expr' c g a
  App' :: Expr' c g (a ':-> b) -> Expr' c g a -> Expr' c g b
  Abs' :: Expr' c (g ':* a) b -> Expr' c g (a ':-> b)

-- newtype PSh c g = PSh (g t -> a t)

-- type (a :*: b) k g = (a k g, b k g)
-- type (a :+: b) k g = Either (a k g) (b k g)
-- type (a :->: b) k g = forall d. Extends k g d => a k d -> b k d
compile :: CCC c => Expr' c g a -> c g a
compile (Const' x) = x
compile (App' f x) = appl (compile f) (compile x)
compile (Abs' f) = abstract (compile f)