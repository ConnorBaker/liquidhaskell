{-@ LIQUID "--expect-any-error" @-}
-- | `tcons` pins which Char was consed, not just that one was.
module Text02 where

import Data.Text

{-@ consWrongChar :: c : Char -> d : Char -> t : Text -> { v : Text | v == tcons d t } @-}
consWrongChar :: Char -> Char -> Text -> Text
consWrongChar c _ t = Data.Text.cons c t
