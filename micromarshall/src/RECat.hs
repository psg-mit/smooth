{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fplugin=ConCat.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:trace #-}
{-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:showResiduals #-}
{-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:showCcc #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}

module RECat where

import Data.Number.MPFR (MPFR)
import Data.Constraint ((:-) (Sub), Dict (Dict))

import Prelude hiding (id, (.))
import RealExpr
import ConCat.AltCat (toCcc)
import ConCat.Rebox ()
import ConCat.Category
import ConCat.Misc hiding ((<~),(~>),type (&&))

instance Category RFunc where
  type Ok RFunc = Approx
  id = eid
  (.) = flip ecompose

instance OpCon (Prod RFunc) (Sat Approx) where
  inOp = Entail (Sub Dict)

instance ProductCat RFunc where
  exl = efst
  exr = esnd
  dup = edup

instance TerminalCat RFunc where
  it = econst ()

test :: RFunc () MPFR
-- test = toCcc (\x -> eplus (econstD 1) (econstD 2))
test = ap2 eplus (econstD 1) (econstD 2)