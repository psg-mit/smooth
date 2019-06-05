{-# OPTIONS_GHC -fplugin=ConCat.Plugin #-}
--  {-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:trace #-}
{-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:showResiduals #-}
{-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:showCcc #-}
{-# OPTIONS_GHC -fsimpl-tick-factor=1000 #-}
{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}

module RECat where

import qualified Data.Number.MPFR as M
import Data.Number.MPFR (MPFR)
import Data.Constraint ((:-) (Sub), Dict (Dict))

import Prelude hiding (id, (.))
import RealExpr
import ConCat.AltCat (toCcc)
import ConCat.Rebox ()
import ConCat.Category
import ConCat.Misc hiding ((<~),(~>),type (&&))
import qualified Interval as I
import qualified Rounded as R

import GHC.Generics

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

instance Approx a => ConstCat RFunc a where
  const = econst

instance MonoidalPCat RFunc where
  RFunc f1 a1 p1 *** RFunc f2 a2 p2 = RFunc (\(CompactPair i1 i2) (p1, p2) -> CompactPair (f1 i1 p1) (f2 i2 p2)) (CompactPair a1 a2) (p1, p2)

instance NumCat RFunc MPFR where
  addC = eplus
  mulC = emul
  negateC = RFunc (\(CompactMPFR i) p -> CompactMPFR (I.inegate p i)) RealExpr.bottom 1

class RealCat k where
  rplus :: (MPFR, MPFR) `k` MPFR
  rmul :: (MPFR, MPFR) `k` MPFR
  rnegate :: MPFR `k` MPFR

instance RealCat (->) where

instance RealCat RFunc where
  rplus = eplus
  rmul = emul
  rnegate = RFunc (\(CompactMPFR i) p -> CompactMPFR (I.inegate p i)) RealExpr.bottom 1

instance Num MPFR where
  (+) = R.add 10 R.Down

test1 :: () -> MPFR
test1 () = addC (k 1, k 2)
  where
  k = M.fromDouble M.Down 10

test :: RFunc () MPFR
test = toCcc test1
-- test = ap2 eplus (econstD 1) (econstD 2)