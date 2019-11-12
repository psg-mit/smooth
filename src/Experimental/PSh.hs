{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}


{-- Presheaves -}
module Experimental.PSh where
import Control.Category (Category)
import qualified Control.Category as C
import GHC.Exts (Constraint)

class ConCat k where
  type Ok k a :: Constraint
  id :: Ok k a => k a a
  (.) :: Ok k c => k b c -> k a b -> k a c

infixl 7 :*
data (a :* b) g = a g :* b g
infixl 6 :+
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

-- Function application
(#) :: Category k => Arr k a b g -> a g -> b g
Arr f # x = f C.id x

unArr :: Arr k (R k a) (R k b) g -> forall d. k d g -> k d a -> k d b
unArr (Arr f) g x = y where
  R y = f g (R x)

lift2 :: (forall g. a g -> b g -> c g) -> Arr k d a g -> Arr k d b g -> Arr k d c g
lift2 op (Arr f) (Arr g) = Arr $ \d x -> op (f d x) (g d x)

lift1' :: (forall g. a g -> b g) -> Arr k d a g -> Arr k d b g
lift1' op (Arr f) = Arr $ \d x -> op (f d x)