import Prelude
import Types.Real
import Types.Maximizer
import RealExpr (runPoint)
import FwdMode (getValue)
import SmoothLang (runDerivVarianceLinearChange)

main :: IO ()
main = print runDerivVarianceLinearChange
-- mapM_ print . runPoint . getValue $ x
--   where
--   R x = exampleHausdorffDistDeriv :: DReal ()