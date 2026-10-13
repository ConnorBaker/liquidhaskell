{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module TextOrdGood where

import Data.Text (Text)
import Data.Text qualified as Text

newtype CheckedText = CheckedText Text
    deriving newtype (Eq, Ord)

{-@ data CheckedText = CheckedText { checkedText :: {t:Text | tbounds t} } @-}

chooseMin, chooseMax :: CheckedText -> CheckedText -> CheckedText
chooseMin = min
chooseMax = max

{-@ selectMin :: x:{Text | tbounds x} -> y:{Text | tbounds y}
              -> {v:Text | tbounds v && (v == x || v == y)} @-}
selectMin :: Text -> Text -> Text
selectMin = min

{-@ selectMax :: x:{Text | tbounds x} -> y:{Text | tbounds y}
              -> {v:Text | tbounds v && (v == x || v == y)} @-}
selectMax :: Text -> Text -> Text
selectMax = max

genericMin, genericMax :: Ord a => a -> a -> a
genericMin = min
genericMax = max
{-# NOINLINE genericMin #-}
{-# NOINLINE genericMax #-}

{-@ selectGenericMin :: x:{Text | tbounds x} -> y:{Text | tbounds y}
                     -> {v:Text | tbounds v} @-}
selectGenericMin :: Text -> Text -> Text
selectGenericMin = genericMin

{-@ selectGenericMax :: x:{Text | tbounds x} -> y:{Text | tbounds y}
                     -> {v:Text | tbounds v} @-}
selectGenericMax :: Text -> Text -> Text
selectGenericMax = genericMax

{-@ compareBounded :: {t:Text | tbounds t} -> {t:Text | tbounds t} -> Ordering @-}
compareBounded :: Text -> Text -> Ordering
compareBounded = compare

-- Selection preserves either domain; it neither needs nor creates UTF-8.
{-@ selectValid :: x:{Text | tvalid x} -> y:{Text | tvalid y}
                -> {v:Text | tvalid v} @-}
selectValid :: Text -> Text -> Text
selectValid = min

{-@ selectMalformed :: x:{Text | tbounds x && not (tutf8 x)}
                    -> y:{Text | tbounds y && not (tutf8 y)}
                    -> {v:Text | tbounds v && not (tutf8 v)} @-}
selectMalformed :: Text -> Text -> Text
selectMalformed = max

{-@ splitValidity :: t:{Text | tvalid t} -> {v:Text | tbounds v && tutf8 v} @-}
splitValidity :: Text -> Text
splitValidity text = text

{-@ joinValidity :: t:{Text | tbounds t && tutf8 t} -> {v:Text | tvalid v} @-}
joinValidity :: Text -> Text
joinValidity text = text

inhabited :: CheckedText
inhabited = chooseMin (CheckedText Text.empty) (chooseMax (CheckedText Text.empty) (CheckedText Text.empty))
