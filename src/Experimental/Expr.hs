{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures, MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE TypeOperators, RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Experimental.Expr where

import Prelude
import Control.Arrow (Arrow, arr)
import Control.Category (Category)
import qualified Control.Category as C
import Unsafe.Coerce

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

-- PHOAS
data Expr (var :: (* -> *) -> *) (c :: * -> * -> *) :: (* -> *) -> * where
  Var :: var a -> Expr var c a
  Const :: PSh c a => (forall d. a d) -> Expr var c a
  App :: Expr var c (Arr c a b) -> Expr var c a -> Expr var c b
  Abs :: PSh c a => (var a -> Expr var c b) -> Expr var c (Arr c a b)

mapVar :: (forall a. var a -> var' a) -> (forall a. var' a -> var a) -> Expr var c g -> Expr var' c g
mapVar f f' e = case e of
  Var x -> Var (f x)
  Const e' -> Const e'
  App g y -> App (mapVar f f' g) (mapVar f f' y)
  Abs g -> Abs (\x -> mapVar f f' (g (f' x)))

-- de Bruijn
data Expr' (c :: * -> * -> *) :: (* -> *) -> (* -> *) -> * where
  Const' :: (forall d. Arr c g a d) -> Expr' c a g
  App' :: Expr' c (Arr c a b) g -> Expr' c a g -> Expr' c b g
  Abs' :: PSh c a => Expr' c b (g :* a) -> Expr' c (Arr c a b) g

data Var c g a where
  Var' :: (forall d. Arr c g a d) -> Var c g a

constArr :: PSh c a => a d -> Arr c g a d
constArr x = Arr (\d _ -> pmap d x)

sndArr :: Var c (g :* a) a
sndArr = Var' (Arr (\d (x :* y) -> y))

fstArr :: Var c (g :* a) g
fstArr = Var' (Arr (\d (x :* y) -> x))

arrCompose :: Arr k b c g -> Arr k a b g -> Arr k a c g
arrCompose (Arr g) (Arr f) = Arr (\d x -> g d (f d x))

varCompose :: Var k b c -> Var k a b -> Var k a c
varCompose (Var' g) (Var' f) = Var' (arrCompose g f)

newtype SomeHom c = SomeHom (forall a b. c a b)
newtype SomeVar c = SomeVar (forall g a. Var c g a)

coerceVar :: Var c a b -> Var c a' b'
coerceVar = unsafeCoerce

indexToVMap :: Int -> SomeVar c
indexToVMap 0 = SomeVar (coerceVar sndArr)
indexToVMap k = case indexToVMap (k - 1) of
  SomeVar a -> SomeVar (coerceVar (varCompose a fstArr))

newtype KInt (a :: * -> *) = KInt Int
  deriving (Num)

-- go from PHOAS to de Bruijn
phoas' :: Int -> Expr KInt c a -> Expr' c a g
phoas' n (Var (KInt i)) = case indexToVMap (n - i - 1) of
  SomeVar a -> case coerceVar a of
    Var' f -> Const' f
phoas' n (Const x) = Const' (constArr x)
phoas' n (App f x) = App' (phoas' n f) (phoas' n x)
phoas' n (Abs f) = let y = f (KInt n) in let z = phoas' (n + 1) y in Abs' z

phoas :: Expr KInt c a -> Expr' c a g
phoas = phoas' 0

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

constFunc :: k ~ (->) => Expr var k (Arr k (R k a) (Arr k (R k b) (R k a)))
constFunc = Abs (\x -> Abs (\y -> Var x))

constFuncCompiled :: k ~ (->) => (Arr k (R k a) (Arr k (R k b) (R k a))) g
constFuncCompiled = compile (phoas constFunc) (R (\_ -> ()))

convolutedTwo :: k ~ (->) => Expr var k (R k Int)
convolutedTwo = App
  (App
  (App (Abs (\x -> Abs (\y -> Abs (\z -> Var x))))
  (Const (R (\_ -> 2))))
  (Const (R (\_ -> 15))))
  (Const (R (\_ -> 3)))

justTwo :: Int
justTwo = case compile (phoas convolutedTwo) (R (\_ -> ())) of
  R f -> f ()