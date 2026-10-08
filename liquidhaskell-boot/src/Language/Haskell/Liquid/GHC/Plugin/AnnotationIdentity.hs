module Language.Haskell.Liquid.GHC.Plugin.AnnotationIdentity (
    AnnotationIdentityError (..),
    selectAnnotationPayload,
    annotationIdentityError,
) where

import Data.Typeable (TypeRep, tyConModule, tyConName, tyConPackage, typeRepTyCon)
import Data.Word (Word8)
import GHC.Serialized (Serialized (..))

data AnnotationIdentityError
    = StaleAnnotationUnit String String
    | DuplicateAnnotations
    deriving (Eq, Show)

{- | Select an annotation of the exact expected nominal type. The caller must
first restrict annotations to the intended module target. Matching the type
constructor's module/name under a different unit is evidence only for an
incompatibility error, never authority to decode its payload.

Payloads are deliberately opaque here: recognized corrupt bytes must reach
the codec and produce its error, rather than masquerading as missing metadata.
-}
selectAnnotationPayload :: TypeRep -> [Serialized] -> Either AnnotationIdentityError (Maybe [Word8])
selectAnnotationPayload expected = go Nothing
  where
    expectedTyCon = typeRepTyCon expected
    go found [] = Right found
    go found (Serialized actual bytes : rest)
        | actual == expected = case found of
            Nothing -> go (Just bytes) rest
            Just _ -> Left DuplicateAnnotations
        | stale actual = Left (StaleAnnotationUnit (tyConPackage expectedTyCon) (tyConPackage (typeRepTyCon actual)))
        | otherwise = go found rest
    stale actual =
        let actualTyCon = typeRepTyCon actual
         in tyConModule actualTyCon == tyConModule expectedTyCon
                && tyConName actualTyCon == tyConName expectedTyCon
                && tyConPackage actualTyCon /= tyConPackage expectedTyCon

annotationIdentityError :: AnnotationIdentityError -> String
annotationIdentityError (StaleAnnotationUnit expected actual) =
    "LiquidHaskell annotation uses incompatible compiler unit "
        ++ show actual
        ++ "; expected "
        ++ show expected
        ++ ". Rebuild the dependency with the current LiquidHaskell compiler."
annotationIdentityError DuplicateAnnotations =
    "Multiple LiquidHaskell annotations for one module; rebuild the dependency with the current LiquidHaskell compiler."
