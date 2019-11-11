module Types.Bijection where

import Control.Category

infix 2 :==

data (:==) a b = Bijection
  { from :: a -> b
  , to :: b -> a
  }