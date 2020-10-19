import Prelude
import Control.Monad (forM_)
import SmoothLang

main :: IO ()
main = forM_
  [ ("runDerivIntegralRelu", runDerivIntegralRelu)
  , ("runRaytraceExample", runRaytraceExample)
  , ("runRaytraceExampleDeriv", runRaytraceExampleDeriv)
  , ("runDerivTStar", runDerivTStar)
  , ("runDerivTStarAnalytic", runDerivTStarAnalytic)
  , ("runReluFirstDerivAt0", runReluFirstDerivAt0)
  , ("runDerivBrightness", runDerivBrightness)
  , ("runDerivMeanLinearChange", runDerivMeanLinearChange)
  , ("runDerivVarianceLinearChange", runDerivVarianceLinearChange)
  , ("runHausdorffDistCircleL", runHausdorffDistCircleL)
  , ("runHausdorffDistTranslatedQuarterCircle", runHausdorffDistTranslatedQuarterCircle)
  ] $ \(name, value) -> do
    putStrLn name
    print value