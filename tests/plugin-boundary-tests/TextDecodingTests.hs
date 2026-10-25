module TextDecodingTests (tests) where

import CompilerFixture
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase)

-- Data.Text.strip requires valid Text. text's decodeUtf8With returns valid Text
-- for every handler (the trusted contract in Data.Text.Encoding_LHAssumptions),
-- so a lenient or arbitrary-handler decoding meets that premise. Text with no
-- producer contract does not: a byte slice of valid Text may split a scalar,
-- and an unrefined parameter may be any Text. The fact states validity only:
-- it makes no contradiction provable after a decoding and gives no byte count.
tests :: (FilePath -> IO FilePath) -> IO Compiler -> Optimization -> TestTree
tests fixture compiler optimization =
    testGroup
        "decoded text validity"
        [ check "lenient and arbitrary-handler decodings meet strip's premise" "DecodedStrip" Safe
        , check "a byte slice and an arbitrary Text do not" "UndecodedStrip" (UnsafeAt [10, 14])
        , check "a decoding does not prove false" "DecodedVacuity" (UnsafeAt [11])
        , check "a decoding states no byte count" "DecodedSize" (UnsafeAt [10])
        ]
  where
    check label name expected = testCase label $ withSystemTempDirectory "lh-text-decoding" $ \directory -> do
        tool <- compiler
        copyFixture fixture ("plugin-boundary-tests/fixtures/text-decoding" </> name ++ ".hs") directory name
        _ <- compile tool Strict optimization ObjectCode directory name [] [] expected
        pure ()
