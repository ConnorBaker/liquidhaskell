{-# OPTIONS_GHC -O1 #-}

-- | Only the fields GHC actually unpacked may be expanded.
--
-- @expandProductType@ rewrites a constructor's spec to the WORKER's argument
-- types, and it decided what to rewrite by asking whether
-- @deepSplitProductType@ could take a field apart. That is strictly more than
-- @-funbox-small-strict-fields@ does: `Data.Text.Text` is a
-- single-constructor type with THREE fields, so it splits perfectly well and
-- GHC leaves it entirely alone.
--
-- 'Frame' below is the shape that makes the two disagree -- a `Text` GHC does
-- not touch beside an @!Int@ it does -- and it is not a contrived one; it is
-- the shape of a parser's continuation frame. Expanding the `Text` puts three
-- arguments in the spec where the worker has one, and every field after it
-- lands one position out: measured, this module is rejected with
-- @Illegal type specification for `Frame`@, quoting a `Text`-typed binder
-- carrying the @Int@ field's @v <= flim@ refinement.
--
-- The two-field and three-field prefixes of the same record are the quieter
-- half and the reason the criterion is per FIELD rather than per constructor:
-- there the misalignment does not change the argument count enough to be
-- rejected, and the module is merely UNSAFE at 'useFrame', with 'frameLength''s
-- bound silently gone.
--
-- @-O1@ is required, as for its siblings: below it the worker's type still
-- equals the spec's and @expandProductType@ never runs.
module UnpackedFieldReftMixed where

import Data.Text (Text)

{-@ inline flim @-}
flim :: Int
flim = 1024 * 1024

{-@ data Frame = Frame Text {v : Int | v <= flim} [Text] Text Text @-}
data Frame = Frame !Text !Int ![Text] !Text !Text

{-@ needBounded :: {v : Int | v <= flim} -> Int @-}
needBounded :: Int -> Int
needBounded x = x

useFrame :: Frame -> Int
useFrame (Frame _ n _ _ _) = needBounded n
