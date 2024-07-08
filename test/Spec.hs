import Test.Hspec
import qualified CoreToZincSpec as CTZ
import qualified StlcTypeInference as STI

main :: IO ()
main = hspec $ do
    describe "Test CoreToZincSpec"      CTZ.spec
    describe "Test StlcTypeInference"   STI.spec
