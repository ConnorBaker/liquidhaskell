module Language.Haskell.Liquid.GHC.Plugin.AnnotationCodec (
    encodePayload,
    decodePayload,
) where

import qualified Codec.Compression.Zstd as Zstd
import qualified Data.Binary.Get as Get
import qualified Data.Binary.Put as Put
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import GHC.Utils.Fingerprint (Fingerprint (..), fingerprintByteString)

-- The marker identifies this wire format, not a Haskell type. The annotation's
-- LiquidLibBytes declaration remains unchanged, but its defining package unit
-- can change. AnnotationIdentity checks that boundary. No legacy decoding is done.
magic :: BS.ByteString
magic = BS.pack [76, 72, 83, 112, 101, 99, 90, 0]

encodePayload :: BS.ByteString -> BS.ByteString
encodePayload input =
    -- A uniform reversible prefix keeps even the empty payload in the strict
    -- zstd API's known, nonempty-frame domain. Skip is never interpreted as data.
    let compressed = Zstd.compress 3 (BS.cons 0 input)
        Fingerprint hi lo = fingerprintByteString compressed
        header = Put.runPut $ do
            Put.putByteString magic
            Put.putWord8 1
            Put.putWord64be (fromIntegral $ BS.length input)
            Put.putWord64be (fromIntegral $ BS.length compressed)
            Put.putWord64be hi
            Put.putWord64be lo
     in BL.toStrict (header <> BL.fromStrict compressed)

-- The fingerprint detects accidental wire corruption; it is not authentication.
-- Check body length and fingerprint before asking zstd to allocate its output.
decodePayload :: BS.ByteString -> Either String BS.ByteString
decodePayload input
    | BS.length input < BS.length magic = invalid "truncated header"
    | BS.take (BS.length magic) input /= magic =
        invalid "obsolete or unrecognized wire format"
    | otherwise = case Get.runGetOrFail header (BL.fromStrict input) of
        Left _ -> invalid "truncated header"
        Right (rest, _, (version, outputSize, bodySize, expectedFingerprint))
            | version /= 1 -> invalid "unsupported wire version"
            | toInteger outputSize >= toInteger (maxBound :: Int) ->
                invalid "unrepresentable decoded size"
            | toInteger bodySize /= toInteger (BL.length rest) ->
                invalid "compressed body length mismatch"
            | otherwise ->
                let compressed = BL.toStrict rest
                 in if fingerprintByteString compressed /= expectedFingerprint
                        then invalid "compressed body fingerprint mismatch"
                        else case Zstd.decompressedSize compressed of
                            Just size | toInteger size == toInteger outputSize + 1 ->
                                case Zstd.decompress compressed of
                                    Zstd.Decompress output
                                        | BS.length output /= size -> invalid "decoded body length mismatch"
                                        | Just (0, bytes) <- BS.uncons output -> Right bytes
                                        | otherwise -> invalid "invalid decoded framing marker"
                                    Zstd.Error message -> invalid ("zstd decompression failed: " ++ message)
                                    Zstd.Skip -> invalid "zstd payload contains no data frame"
                            _ -> invalid "zstd frame size does not match the header"
  where
    header = do
        _ <- Get.getByteString (BS.length magic)
        version <- Get.getWord8
        outputSize <- Get.getWord64be
        bodySize <- Get.getWord64be
        hi <- Get.getWord64be
        lo <- Get.getWord64be
        pure (version, outputSize, bodySize, Fingerprint hi lo)

invalid :: String -> Either String a
invalid reason =
    Left $
        "LiquidHaskell annotation: "
            ++ reason
            ++ "; recompile the dependency with the current LiquidHaskell."
