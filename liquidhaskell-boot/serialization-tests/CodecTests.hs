module CodecTests (tests) where

import qualified Codec.Compression.Zstd as Zstd
import Control.Monad (forM_)
import qualified Data.Binary.Put as Put
import Data.Bits (xor)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import Data.List (isInfixOf)
import Data.Word (Word64, Word8)
import GHC.Utils.Fingerprint (Fingerprint (..), fingerprintByteString)
import Language.Haskell.Liquid.GHC.Plugin.AnnotationCodec
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
    testGroup
        "annotation codec"
        [ testCase "empty roundtrip" $ roundtrip BS.empty
        , testCase "all byte values roundtrip" $ roundtrip (BS.pack [0 .. 255])
        , testCase "varied lengths roundtrip" $
            forM_ [1, 255, 256, 257, 4096] $
                \size -> roundtrip (BS.pack $ take size $ cycle [0 .. 255])
        , testCase "repeated declaration bytes roundtrip" $ roundtrip repeated
        , testCase "compresses repeated data" $
            assertBool "compressed envelope is smaller" (BS.length wire < BS.length repeated)
        , testCase "obsolete payload is rejected" $
            rejects "obsolete or unrecognized" (BS.pack [0 .. 255])
        , testCase "short marker is rejected" $
            rejects "truncated header" (BS.take 7 wire)
        , testCase "truncated versioned header is rejected" $
            rejects "truncated header" (BS.take 40 wire)
        , testCase "unknown version is rejected" $
            rejects "unsupported wire version" (change 8 wire)
        , testCase "truncated compressed body is rejected" $
            rejects "body length mismatch" (BS.init wire)
        , testCase "trailing bytes are rejected" $
            rejects "body length mismatch" (wire <> BS.singleton 0)
        , testCase "changed compressed body is rejected" $
            rejects "fingerprint mismatch" (change 42 wire)
        , testCase "changed fingerprint is rejected" $
            rejects "fingerprint mismatch" (change 40 wire)
        , testCase "changed decoded length is rejected before decompression" $
            rejects "frame size does not match" (change 16 wire)
        , testCase "unrepresentable decoded length is rejected" $
            rejects "unrepresentable decoded size" (replace 9 255 wire)
        , testCase "valid fingerprint does not admit malformed zstd" $
            rejects "frame size does not match" (framed 1 $ BS.pack [1 .. 8])
        , testCase "valid fingerprint does not admit a skippable frame" $
            rejects "frame size does not match" (framed 0 $ BS.pack [0x50, 0x2a, 0x4d, 0x18, 0, 0, 0, 0])
        , testCase "valid fingerprint does not admit truncated zstd" $
            rejects "zstd decompression failed" (framed 256000 $ BS.init $ Zstd.compress 3 $ BS.cons 0 repeated)
        , testCase "valid fingerprint does not admit incorrect decoded framing" $
            rejects "invalid decoded framing marker" (framed 2 $ Zstd.compress 3 $ BS.pack [1, 2, 3])
        ]
  where
    repeated = BS.concat (replicate 1000 $ BS.pack [0 .. 255])
    wire = encodePayload repeated

roundtrip :: BS.ByteString -> Assertion
roundtrip bytes = decodePayload (encodePayload bytes) @?= Right bytes

rejects :: String -> BS.ByteString -> Assertion
rejects expected bytes = case decodePayload bytes of
    Left message -> assertBool message (expected `isInfixOf` message)
    Right _ -> assertFailure ("accepted invalid payload: " ++ expected)

change :: Int -> BS.ByteString -> BS.ByteString
change offset bytes = replace offset (BS.index bytes offset `xor` 1) bytes

replace :: Int -> Word8 -> BS.ByteString -> BS.ByteString
replace offset byte bytes = BS.take offset bytes <> BS.singleton byte <> BS.drop (offset + 1) bytes

-- Construct a correctly checksummed envelope around deliberately invalid codec
-- input, so these tests reach past the envelope's corruption checks.
framed :: Word64 -> BS.ByteString -> BS.ByteString
framed outputSize body =
    let Fingerprint hi lo = fingerprintByteString body
        header = Put.runPut $ do
            Put.putByteString (BS.take 9 $ encodePayload BS.empty)
            Put.putWord64be outputSize
            Put.putWord64be (fromIntegral $ BS.length body)
            Put.putWord64be hi
            Put.putWord64be lo
     in BL.toStrict (header <> BL.fromStrict body)
