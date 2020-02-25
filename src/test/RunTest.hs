import Prelude
import Types.Real
import Types.Maximizer
import RealExpr (runPoint)
import FwdMode (getValue)

main :: IO ()
main = mapM_ print . runPoint . getValue $ x
  where
  R x = exampleHausdorffDistDeriv :: DReal ()