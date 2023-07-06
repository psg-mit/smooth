import Demo
import Control.Monad (forM_)


main :: IO ()
main = forM_
  [ ("it1", it1)
  , ("it2", it2)
  , ("it3", it3)
  , ("it4", it4)
  , ("it5", it5)
  , ("it6", it6)
  , ("it7", it7)
  , ("it8", it8)
  , ("it9", it9)
  ] $ \(name, value) -> do
    putStrLn name
    print value