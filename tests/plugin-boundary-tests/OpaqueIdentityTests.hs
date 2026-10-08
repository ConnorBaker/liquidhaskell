module OpaqueIdentityTests (tests) where

import CompilerFixture
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase)

tests :: IO Compiler -> Optimization -> TestTree
tests compiler optimization =
    testGroup
        "imported opaque callable identities"
        [ sourceCase "ByteStringIdentity" byteStringIdentity Safe
        , sourceCase "ByteStringZeroLengthFalse" byteStringZeroLengthFalse (UnsafeAt [7])
        , sourceCase "ByteStringEmptyReturnFalse" byteStringEmptyReturnFalse (UnsafeAt [7])
        , sourceCase "OpaqueUnannotatedPartial" opaqueUnannotatedPartial (UnsafeAt [4])
        , testCase "original external owner and generic callable contracts" $
            withSystemTempDirectory "lh-opaque-owner" $ \directory -> do
                tool <- compiler
                let provider = directory </> "producer"
                writeFixture "opaque owner" provider "OpaqueOwnerProducer" opaqueOwnerProducer
                checked <- compile tool Strict optimization ObjectCode provider "OpaqueOwnerProducer" [] ["--higherorder"] Safe
                assertPublication tool checked True
                mapM_
                    (\(name, body, expected) -> run tool (directory </> name) name body [provider </> "objects"] expected)
                    [ ("OpaqueOwnerGood", opaqueOwnerGood, Safe)
                    , ("OpaqueOwnerInputFalse", opaqueOwnerInputFalse, UnsafeAt [5])
                    , ("OpaqueOwnerResultFalse", opaqueOwnerResultFalse, UnsafeAt [5])
                    , ("OpaqueOwnerCallbackFalse", opaqueOwnerCallbackFalse, UnsafeAt [5])
                    ]
        , testCase "private opaque domain survives GHC interface availability" $
            withSystemTempDirectory "lh-opaque-private" $ \directory -> do
                tool <- compiler
                let provider = directory </> "producer"
                writeFixture "private opaque" provider "OpaquePrivateProducer" opaquePrivateProducer
                checked <- compile tool Strict optimization ObjectCode provider "OpaquePrivateProducer" [] ["--higherorder"] Safe
                assertPublication tool checked True
                -- GHC omits interface pragmas at O0 but retains this private
                -- owner through public's unfolding at O2. Its input domain
                -- must govern the identical clients in either environment.
                case optimization of
                    O0 -> assertSourceNameAbsent tool checked "hidden"
                    O2 -> assertSourceNamePresent tool checked "hidden"
                run tool (directory </> "client") "OpaquePrivateClient" opaquePrivateClient [provider </> "objects"] Safe
                run tool (directory </> "false") "OpaquePrivateDomainFalse" opaquePrivateDomainFalse [provider </> "objects"] (UnsafeAt [3])
        , testCase "logical-only private opaque payload has no runtime declaration" $
            withSystemTempDirectory "lh-opaque-logical-only" $ \directory -> do
                tool <- compiler
                let provider = directory </> "producer"
                writeFixture "logical-only private opaque" provider "OpaqueLogicalOnlyProducer" opaqueLogicalOnlyProducer
                checked <- compile tool Strict optimization ObjectCode provider "OpaqueLogicalOnlyProducer" [] ["--higherorder"] Safe
                assertPublication tool checked True
                assertSourceNameAbsent tool checked "logicalOnlyHidden"
                run tool (directory </> "client") "OpaqueLogicalOnlyClient" opaqueLogicalOnlyClient [provider </> "objects"] Safe
        , testCase "logical-only opaque inputs retain native domains and result carriers" $
            withSystemTempDirectory "lh-opaque-scoped" $ \directory -> do
                tool <- compiler
                let provider = directory </> "producer"
                writeFixture "scoped opaque" provider "OpaqueScopedProducer" opaqueScopedProducer
                checked <- compile tool Strict optimization ObjectCode provider "OpaqueScopedProducer" [] ["--higherorder"] Safe
                assertPublication tool checked True
                mapM_ (assertSourceNameAbsent tool checked) ["hiddenPartial", "hiddenCallback", "hiddenPoly", "hiddenByte", "hiddenEq", "hiddenBox", "hiddenSink"]
                mapM_
                    (\(name, body, expected) -> run tool (directory </> name) name body [provider </> "objects"] expected)
                    [ ("OpaqueScopedGood", opaqueScopedGood, Safe)
                    , ("OpaqueScopedDomainFalse", opaqueScopedDomainFalse, UnsafeAt [3])
                    , ("OpaqueScopedCallbackFalse", opaqueScopedCallbackFalse, UnsafeAt [7])
                    , ("OpaqueScopedWrongCarrier", opaqueScopedWrongCarrier, FormationRefusal 3 "GHC-83865")
                    , ("OpaqueScopedMissingEvidence", opaqueScopedMissingEvidence, FormationRefusal 3 "No instance for ‘Eq a’")
                    , ("OpaqueScopedBox", opaqueScopedUnsupported "OpaqueScopedBox" "BoxLaw", FormationRefusal 3 "supported native result-domain metadata")
                    , ("OpaqueScopedSink", opaqueScopedUnsupported "OpaqueScopedSink" "SinkLaw", FormationRefusal 3 "supported native result-domain metadata")
                    ]
        ]
  where
    sourceCase name body expected =
        testCase name $ withSystemTempDirectory "lh-opaque-default" $ \directory -> do
            tool <- compiler
            run tool directory name body [] expected
    run tool directory name body imports expected = do
        writeFixture name directory name body
        _ <- compile tool Strict optimization ObjectCode directory name imports ["--higherorder"] expected
        pure ()

byteStringIdentity :: String
byteStringIdentity =
    unlines
        [ "module ByteStringIdentity where"
        , "import Data.ByteString (ByteString)"
        , "import Data.ByteString qualified as B"
        , "import Data.Word (Word8)"
        , "{-@ observe :: bytes:ByteString -> {out:[Word8] | out == B.unpack bytes && len out == bslen bytes} @-}"
        , "observe :: ByteString -> [Word8]"
        , "observe bytes = B.unpack bytes"
        ]

byteStringZeroLengthFalse :: String
byteStringZeroLengthFalse =
    unlines
        [ "module ByteStringZeroLengthFalse where"
        , "import Data.ByteString (ByteString)"
        , "import Data.ByteString qualified as B"
        , "import Data.Word (Word8)"
        , "{-@ observe :: bytes:{ByteString | bslen bytes > 0} -> {out:[Word8] | out == B.unpack bytes && len out == 0} @-}"
        , "observe :: ByteString -> [Word8]"
        , "observe bytes = B.unpack bytes"
        ]

byteStringEmptyReturnFalse :: String
byteStringEmptyReturnFalse =
    unlines
        [ "module ByteStringEmptyReturnFalse where"
        , "import Data.ByteString (ByteString)"
        , "import Data.ByteString qualified as B"
        , "import Data.Word (Word8)"
        , "{-@ observe :: bytes:{ByteString | bslen bytes > 0} -> {out:[Word8] | out == B.unpack bytes && len out == bslen bytes} @-}"
        , "observe :: ByteString -> [Word8]"
        , "observe _ = []"
        ]

opaqueOwnerProducer :: String
opaqueOwnerProducer =
    unlines
        [ "module OpaqueOwnerProducer (generic, step, apply) where"
        , "import Prelude"
        , "import Prelude qualified as P"
        , "{-@ opaque-reflect P.id @-}"
        , "{-@ opaque-reflect generic @-}"
        , "{-@ opaque-reflect step @-}"
        , "{-@ generic :: a -> a @-}"
        , "generic :: a -> a"
        , "generic x = x"
        , "{-@ step :: x:{Integer | x > 0} -> {v:Integer | v > x} @-}"
        , "step :: Integer -> Integer"
        , "step x = x + 1"
        , "{-@ opaque-reflect apply @-}"
        , "{-@ apply :: f:(x:Integer -> {v:Integer | v >= x}) -> x:Integer -> {v:Integer | v >= x} @-}"
        , "apply :: (Integer -> Integer) -> Integer -> Integer"
        , "apply f x = f x"
        ]

opaqueOwnerGood :: String
opaqueOwnerGood =
    unlines
        [ "module OpaqueOwnerGood where"
        , "import Prelude"
        , "import OpaqueOwnerProducer qualified as O"
        , "import Prelude qualified as P"
        , "{-@ external :: x:a -> {v:a | v == P.id x} @-}"
        , "external :: a -> a"
        , "external x = P.id x"
        , "{-@ generic :: x:a -> {v:a | v == O.generic x} @-}"
        , "generic :: a -> a"
        , "generic x = O.generic x"
        , "{-@ step :: x:{Integer | x > 0} -> {v:Integer | v == O.step x && v > x} @-}"
        , "step :: Integer -> Integer"
        , "step x = O.step x"
        , "{-@ callback :: f:(x:Integer -> {v:Integer | v >= x}) -> x:Integer -> {v:Integer | v == O.apply f x && v >= x} @-}"
        , "callback :: (Integer -> Integer) -> Integer -> Integer"
        , "callback f x = O.apply f x"
        ]

opaqueOwnerInputFalse :: String
opaqueOwnerInputFalse =
    unlines
        [ "module OpaqueOwnerInputFalse where"
        , "import OpaqueOwnerProducer qualified as O"
        , "{-@ bad :: Integer @-}"
        , "bad :: Integer"
        , "bad = O.step 0"
        ]

opaqueOwnerResultFalse :: String
opaqueOwnerResultFalse =
    unlines
        [ "module OpaqueOwnerResultFalse where"
        , "import OpaqueOwnerProducer qualified as O"
        , "{-@ bad :: x:{Integer | x > 0} -> {v:Integer | v == x} @-}"
        , "bad :: Integer -> Integer"
        , "bad x = O.step x"
        ]

opaquePrivateProducer :: String
opaquePrivateProducer =
    unlines
        [ "module OpaquePrivateProducer (public) where"
        , "{-@ opaque-reflect hidden @-}"
        , "{-# NOINLINE hidden #-}"
        , "{-@ hidden :: x:{Integer | x > 0} -> Integer @-}"
        , "hidden :: Integer -> Integer"
        , "hidden x = x"
        , "{-@ predicate PrivateResult X V = V == hidden X @-}"
        , "{-@ predicate PrivateLaw X = hidden X == hidden X @-}"
        , "{-@ public :: x:{Integer | x > 0} -> {v:Integer | PrivateResult x v} @-}"
        , "{-# INLINABLE public #-}"
        , "public :: Integer -> Integer"
        , "public x = if x > 0 then hidden x else 0"
        ]

opaquePrivateClient :: String
opaquePrivateClient =
    unlines
        [ "module OpaquePrivateClient where"
        , "import OpaquePrivateProducer qualified as O"
        , "{-@ call :: x:{Integer | x > 0} -> {v:Integer | O.PrivateResult x v} @-}"
        , "call :: Integer -> Integer"
        , "call x = O.public x"
        ]

opaqueOwnerCallbackFalse :: String
opaqueOwnerCallbackFalse =
    unlines
        [ "module OpaqueOwnerCallbackFalse where"
        , "import OpaqueOwnerProducer qualified as O"
        , "{-@ bad :: x:{Integer | x > 0} -> {v:Integer | v >= x} @-}"
        , "bad :: Integer -> Integer"
        , "bad x = O.apply (\\_ -> 0) x"
        ]

opaquePrivateDomainFalse :: String
opaquePrivateDomainFalse =
    unlines
        [ "module OpaquePrivateDomainFalse where"
        , "import OpaquePrivateProducer qualified as O"
        , "{-@ bad :: {v:Bool | v && O.PrivateLaw 0} @-}"
        , "bad :: Bool"
        , "bad = True"
        ]

opaqueLogicalOnlyProducer :: String
opaqueLogicalOnlyProducer =
    unlines
        [ "module OpaqueLogicalOnlyProducer (public) where"
        , "{-@ opaque-reflect logicalOnlyHidden @-}"
        , "logicalOnlyHidden :: Integer -> Integer"
        , "logicalOnlyHidden x = x"
        , "{-@ predicate LogicalOnlyLaw X = logicalOnlyHidden X == logicalOnlyHidden X @-}"
        , "{-@ public :: x:Integer -> {v:Bool | v && LogicalOnlyLaw x} @-}"
        , "public :: Integer -> Bool"
        , "public _ = True"
        ]

opaqueLogicalOnlyClient :: String
opaqueLogicalOnlyClient =
    unlines
        [ "module OpaqueLogicalOnlyClient where"
        , "import OpaqueLogicalOnlyProducer qualified as O"
        , "{-@ call :: x:Integer -> {v:Bool | v && O.LogicalOnlyLaw x} @-}"
        , "call :: Integer -> Bool"
        , "call x = O.public x"
        ]

opaqueScopedProducer :: String
opaqueScopedProducer =
    unlines
        [ "module OpaqueScopedProducer (public, consumesByte, exposedEq, Box(..), Sink(..)) where"
        , "import Data.Word (Word8)"
        , "data Box a = Box a"
        , "data Sink a = Sink (a -> Integer)"
        , "{-@ opaque-reflect hiddenPartial @-}"
        , "{-@ hiddenPartial :: x:{Integer | x > 0} -> Integer @-}"
        , "hiddenPartial :: Integer -> Integer"
        , "hiddenPartial x = x"
        , "{-@ opaque-reflect hiddenCallback @-}"
        , "{-@ hiddenCallback :: f:(y:{Integer | y >= 0} -> {v:Integer | v >= y}) -> x:{Integer | x >= 0} -> Integer @-}"
        , "hiddenCallback :: (Integer -> Integer) -> Integer -> Integer"
        , "hiddenCallback f x = f x"
        , "{-@ opaque-reflect hiddenPoly @-}"
        , "hiddenPoly :: a -> a"
        , "hiddenPoly x = x"
        , "{-@ opaque-reflect hiddenByte @-}"
        , "hiddenByte :: Word8 -> Word8"
        , "hiddenByte x = x"
        , "{-@ opaque-reflect hiddenEq @-}"
        , "hiddenEq :: Eq a => a -> a"
        , "hiddenEq x = x"
        , "{-@ opaque-reflect exposedEq @-}"
        , "exposedEq :: Eq a => a -> a"
        , "exposedEq x = x"
        , "{-@ opaque-reflect consumesByte @-}"
        , "{-@ consumesByte :: Word8 -> {v:Bool | v} @-}"
        , "consumesByte :: Word8 -> Bool"
        , "consumesByte _ = True"
        , "{-@ opaque-reflect hiddenBox @-}"
        , "{-@ hiddenBox :: Box ({x:Integer | x > 0} -> Integer) @-}"
        , "hiddenBox :: Box (Integer -> Integer)"
        , "hiddenBox = Box (\\x -> x)"
        , "{-@ opaque-reflect hiddenSink @-}"
        , "{-@ hiddenSink :: Sink {x:Integer | x > 0} @-}"
        , "hiddenSink :: Sink Integer"
        , "hiddenSink = Sink (\\x -> x)"
        , "{-@ predicate PartialLaw X = hiddenPartial X == hiddenPartial X @-}"
        , "{-@ predicate CallbackLaw F X = hiddenCallback F X == hiddenCallback F X @-}"
        , "{-@ predicate PolyLaw X = hiddenPoly X == hiddenPoly X @-}"
        , -- The nested application checks the native Word8 result carrier;
          -- reflexivity needs no exported output theorem for either opaque call.
          "{-@ predicate ByteLaw X = consumesByte (hiddenByte X) == consumesByte (hiddenByte X) @-}"
        , "{-@ predicate EqLaw X = hiddenEq X == hiddenEq X @-}"
        , "{-@ predicate BoxLaw = hiddenBox == hiddenBox @-}"
        , "{-@ predicate SinkLaw = hiddenSink == hiddenSink @-}"
        , "public :: Bool"
        , "public = True"
        ]

opaqueScopedGood :: String
opaqueScopedGood =
    unlines
        [ "module OpaqueScopedGood where"
        , "import OpaqueScopedProducer qualified as O"
        , "import Data.Word (Word8)"
        , "{-@ partial :: x:{Integer | x > 0} -> {v:Bool | v && O.PartialLaw x} @-}"
        , "partial :: Integer -> Bool"
        , "partial _ = True"
        , "{-@ callback :: f:(y:{Integer | y >= 0} -> {v:Integer | v >= y}) -> x:{Integer | x >= 0} -> {v:Bool | v && O.CallbackLaw f x} @-}"
        , "callback :: (Integer -> Integer) -> Integer -> Bool"
        , "callback _ _ = True"
        , "{-@ poly :: x:a -> {v:Bool | v && O.PolyLaw x} @-}"
        , "poly :: a -> Bool"
        , "poly _ = True"
        , "{-@ byte :: x:Word8 -> {v:Bool | v && O.ByteLaw x} @-}"
        , "byte :: Word8 -> Bool"
        , "byte _ = True"
        , "{-@ eqLaw :: Eq a => x:a -> {v:Bool | v && O.EqLaw x} @-}"
        , "eqLaw :: Eq a => a -> Bool"
        , "eqLaw _ = True"
        , "{-@ availableEq :: Eq a => x:a -> {v:a | v == O.exposedEq x} @-}"
        , "availableEq :: Eq a => a -> a"
        , "availableEq x = O.exposedEq x"
        ]

opaqueScopedDomainFalse :: String
opaqueScopedDomainFalse =
    unlines
        [ "module OpaqueScopedDomainFalse where"
        , "import OpaqueScopedProducer qualified as O"
        , "{-@ bad :: {v:Bool | v && O.PartialLaw 0} @-}"
        , "bad :: Bool"
        , "bad = True"
        ]

opaqueScopedCallbackFalse :: String
opaqueScopedCallbackFalse =
    unlines
        [ "module OpaqueScopedCallbackFalse where"
        , "import OpaqueScopedProducer qualified as O"
        , "{-@ opaque-reflect zero @-}"
        , "{-@ zero :: Integer -> {v:Integer | v == 0} @-}"
        , "zero :: Integer -> Integer"
        , "zero _ = 0"
        , "{-@ bad :: x:{Integer | x > 0} -> {v:Bool | v && O.CallbackLaw zero x} @-}"
        , "bad :: Integer -> Bool"
        , "bad _ = True"
        ]

opaqueScopedWrongCarrier :: String
opaqueScopedWrongCarrier =
    unlines
        [ "module OpaqueScopedWrongCarrier where"
        , "import OpaqueScopedProducer qualified as O"
        , "{-@ bad :: x:Integer -> {v:Bool | v && O.ByteLaw x} @-}"
        , "bad :: Integer -> Bool"
        , "bad _ = True"
        ]

opaqueScopedUnsupported :: String -> String -> String
opaqueScopedUnsupported name predicate =
    unlines
        [ "module " ++ name ++ " where"
        , "import OpaqueScopedProducer qualified as O"
        , "{-@ bad :: {v:Bool | v && O." ++ predicate ++ "} @-}"
        , "bad :: Bool"
        , "bad = True"
        ]

opaqueScopedMissingEvidence :: String
opaqueScopedMissingEvidence =
    unlines
        [ "module OpaqueScopedMissingEvidence where"
        , "import OpaqueScopedProducer qualified as O"
        , "{-@ bad :: x:a -> {v:Bool | v && O.EqLaw x} @-}"
        , "bad :: a -> Bool"
        , "bad _ = True"
        ]

opaqueUnannotatedPartial :: String
opaqueUnannotatedPartial =
    unlines
        [ "module OpaqueUnannotatedPartial (public) where"
        , "{-@ opaque-reflect hidden @-}"
        , "hidden :: Integer -> Integer"
        , "hidden x = 1 `div` x"
        , "public :: Bool"
        , "public = True"
        ]
