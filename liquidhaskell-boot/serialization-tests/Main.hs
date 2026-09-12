module Main (main) where

import qualified AnnotationIdentityTests
import qualified CodecTests
import qualified Current.IdentityFixture as Current
import qualified Old.IdentityFixture as Old
import Test.Tasty (defaultMain, testGroup)

main :: IO ()
main =
    defaultMain $
        testGroup
            "annotation serialization"
            [ CodecTests.tests
            , AnnotationIdentityTests.tests
            , AnnotationIdentityTests.crossUnitTests Old.payloadType Current.payloadType
            ]
