import Prelude
import FwdPSh (DReal, R (..))
import Types.KShape
import RealExpr (runPoint)
import FwdMode (getValue)

main :: IO ()
main = mapM_ print . runPoint . getValue $ x
  where
  R x = exampleHausdorffDist2 :: DReal ()