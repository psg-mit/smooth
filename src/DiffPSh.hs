{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, IncoherentInstances #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

module DiffPSh where

import Prelude hiding (Real)
import Control.Arrow
import Control.Category (Category)
import qualified Control.Category as C
import Control.Applicative (liftA2)
import Control.Monad (join)
import RealExpr (CMap (..))
import Data.Number.MPFR (MPFR)
import qualified Rounded as R
import Interval (Interval, unitInterval)
import qualified Expr as E
import qualified RealExpr as E
import Experimental.PSh
import Diffeo

type D = (:~>)

instance ConCat D where
  type Ok D a = Additive a
  id = dId
  (.) = (@.)

type Real = R CMap (Interval MPFR)
type DReal = R D (Interval MPFR)

instance R.Rounded a => Num (R CMap (Interval a) g) where
  R x + R y = R (x + y)
  R x * R y = R (x * y)
  negate (R x) = R (negate x)
  R x - R y = R (x - y)
  abs (R x) = R (abs x)
  fromInteger = R Prelude.. fromInteger
  signum (R x) = R (signum x)

instance R.Rounded a => Num (g :~> Interval a) where
  (+) = dap2 add
  D x * D y = D (dMult x y)
  abs = dap1 (lift1 (abs C.id) (signum dId))
  signum = dap1 (lift1 (signum C.id) 0)
  fromInteger x = D $ fromInteger x :# dZero
  negate = dap1 (linearD (negate C.id))

-- instance (PSh k s, VectorSpace v s) => VectorSpace (Arr k a v) s where
--   zeroV   = DiffPSh.constArr zeroV
--   s *^ Arr f = Arr (\d x -> pmap d s *^ f d x)
--   (^+^)   = lift2 (^+^)
--   negateV = lift1' negateV

-- instance (PSh CMap a, R.Rounded b) => Num (D CMap a (R CMap (Interval b)) g) where
--   fromInteger               = dConst . fromInteger
--   D u0 u' + D v0 v'         = D (u0 + v0) (lift2 (+) u' v')
--   D u0 u' - D v0 v'         = D (u0 - v0) (lift2 (-) u' v')
--   u@(D u0 (Arr u')) * v@(D v0 (Arr v')) =
--     D (u0 * v0) (Arr (\g da -> pmap g u * v' g da + u' g da * pmap g v))
--   abs u@(D u0 (Arr u')) = D (abs u0) (Arr (\g da -> pmap g (signum u) * u' g da))
--   -- not totally accurate for signum here, it should blow up at 0...
--   signum (D u u') = D (signum u) (DiffPSh.constArr 0)

instance R.Rounded a => Fractional (R CMap (Interval a) g) where
  recip (R x) = R (recip x)
  fromRational = R Prelude.. fromRational

-- instance (PSh CMap a, R.Rounded b) => Fractional (D CMap a (R CMap (Interval b)) g) where
--   recip = lift1 recip (\u -> - recip (u^2))
--   fromRational = dConst . fromRational

-- Crossing my fingers that this is right!
integrate_unit_interval :: Arr CMap Real Real g -> Real g
integrate_unit_interval f = R $
  E.secondOrderPrim (E.integral' 16 unitInterval) (unArr f (arr fst) (arr snd))

integral1' :: R.Rounded a => CMap (g, Interval a) (Interval a) -> CMap g (Interval a)
integral1' = E.secondOrderPrim (E.integral' 16 unitInterval)

-- integral1 :: R.Rounded a => ((g, Interval a) :~> Interval a) -> (g :~> Interval a)
-- integral1 (D f) = D $ (dWkn integral1' f)

--
integral :: (Arr D DReal DReal) g -> DReal g
integral (Arr f) = undefined -- linearD $ Arr $ \d x -> integrate_unit_interval x

asReal :: R CMap (Interval MPFR) g -> CMap g (Interval MPFR)
asReal (R x) = x

-- example4 :: IO ()
-- example4 = E.runAndPrint $ asReal $
--   getDerivTower (func # 3) !! 1
--   where
--   func :: Sm CMap Real Real g
--   func = Arr $ \g c -> (integral # Arr (\d x -> pmap d c * x ^ 2))