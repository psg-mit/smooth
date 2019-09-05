{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures, MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE TypeOperators, RankNTypes #-}

module Experimental.Expr where

import Prelude
import Control.Arrow (Arrow, arr)
import Control.Category (Category)
import qualified Control.Category as C

data (a :* b) g = a g :* b g
data (a :+ b) g = Inl (a g) | Inr (b g)

data Arr k a b (g :: *) = Arr (forall d. k d g -> a d -> b d)

newtype R k a g = R (k g a)

class PSh k f where
  pmap :: k d g -> f g -> f d

instance Category k => PSh k (R k a) where
  pmap dg (R f) = R (f C.. dg)

instance (PSh k f, PSh k g) => PSh k (f :* g) where
  pmap dg (f :* g) = pmap dg f :* pmap dg g

instance (PSh k f, PSh k g) => PSh k (f :+ g) where
  pmap dg (Inl f) = Inl (pmap dg f)
  pmap dg (Inr g) = Inr (pmap dg g)

instance Category k => PSh k (Arr k a b) where
  pmap cd (Arr f) = Arr (\dg a -> f (cd C.. dg) a)

data Expr (var :: (* -> *) -> *) (c :: * -> * -> *) :: (* -> *) -> * where
  Var :: var a -> Expr var c a
  Const :: PSh c a => (forall d. a d) -> Expr var c a
  App :: Expr var c (Arr c a b) -> Expr var c a -> Expr var c b
  Abs :: (var a -> Expr var c b) -> Expr var c (Arr c a b)

data Expr' (c :: * -> * -> *) :: (* -> *) -> (* -> *) -> * where
  Const' :: (forall d. Arr c g a d) -> Expr' c a g
  App' :: Expr' c (Arr c a b) g -> Expr' c a g -> Expr' c b g
  Abs' :: PSh c a => Expr' c b (g :* a) -> Expr' c (Arr c a b) g

data Var c g a = Var' (forall d. Arr c g a d)

constArr :: PSh c a => a d -> Arr c g a d
constArr x = Arr (\d _ -> pmap d x)

sndArr :: Var c (g :* a) a
sndArr = Var' (Arr (\d (x :* y) -> y))

phoas :: Expr (Var c g) c a -> Expr' c a g
phoas (Var (Var' x)) = Const' x
phoas (Const x) = Const' (constArr x)
phoas (App f x) = App' (phoas f) (phoas x)
-- phoas (Abs f) = let y = f sndArr in let z = phoas y in Abs' z

compile :: PSh c g => Category c => Expr' c a g -> forall d. g d -> a d
compile (Const' (Arr x)) = x C.id
compile (App' f x) = \g -> case (compile f) g of
  Arr h -> let y = compile x g in h C.id y
compile (Abs' f) = \g -> Arr $ (\d x -> compile f (pmap d g :* x))

-- data InList :: * -> [*] -> * where
--   InHere :: InList x (x : xs)
--   InThere :: InList x ys -> InList x (y : ys)

class Extends c g a where
  proj :: c g a

instance Category c => Extends c a a where
  proj = C.id

instance (Arrow c, Extends c g a) => Extends c (g, b) a where
  proj = proj C.. arr fst

var :: Category c => Extends c d g => c g a -> c d a
var x = x C.. proj