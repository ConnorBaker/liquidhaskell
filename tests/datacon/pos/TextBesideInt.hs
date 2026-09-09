{-# OPTIONS_GHC -O1 #-}

-- | Control: @!Text@ -- THREE fields, so @-funbox-small-strict-fields@ leaves
-- it boxed -- beside an unboxed @!Int@, in a two-field record.
--
-- @UnpackedFieldReftMixed.hs@ covers @Text@ only inside a five-field record
-- with a refinement on another field. This is the simplest shape on which
-- "expand only what GHC expanded" can fail: 'mkProductTy' WOULD split @Text@
-- into three components if asked, and 'unpackedFields' reading GHC's own bang
-- is what stops it. @Text@ is not embedded, so an over-expansion is loud.
--
-- A red here would mean the per-field gate fails on the simplest @Text@ shape.
module TextBesideInt where

import Data.Text (Text)

data T = T { tT :: !Text, tN :: !Int }

{-@ measure tN @-}

{-@ mk :: t:Text -> n:Int -> {v:T | tN v == n} @-}
mk :: Text -> Int -> T
mk t n = T t n
