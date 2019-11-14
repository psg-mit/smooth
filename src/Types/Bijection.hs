module Types.Bijection where

import Prelude hiding (id, (.))
import Control.Category

infix 2 :==

data (:==) a b = Bijection
  { from :: a -> b
  , to :: b -> a
  }

instance Category (:==) where
  id = Bijection id id
  Bijection f1 t1 . Bijection f2 t2 = Bijection (f1 . f2) (t2 . t1)

swap :: a :== b -> b :== a
swap (Bijection f g) = Bijection g f