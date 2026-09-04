{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.Text_LHAssumptions where

import Data.Text
import Data.Maybe_LHAssumptions()
import Data.String_LHAssumptions()

-- @tlen@ mirrors @Data.ByteString_LHAssumptions@'s @bslen@, and the length
-- facts below are the @Text@ counterparts of the ones stated there.
--
-- @tappend@ and @tcons@ are DECLARATION-ONLY measures, and so uninterpreted
-- function symbols: the solver knows they are congruent and nothing else. That
-- is what lets a client pin the ORDER of a concatenation. An arithmetic
-- identity over @tlen@ cannot, because @+@ is commutative, so transposing two
-- components still verifies against a sum.
--
-- @Data.Text.toLower@ is @opaque-reflect@ed rather than measured. That puts the
-- REAL function into the logic as an uninterpreted symbol, so a client can
-- spell "already case-folded" as @{ n : Text | n == Data.Text.toLower n }@
-- rather than inventing a predicate of its own.
--
-- Both conjuncts are load-bearing. @v == Data.Text.toLower n@ is the link to
-- the ARGUMENT: the opaque reflection strengthens the signature with it in the
-- defining module, but that strengthening lives in @_gsSig@ and is not part of
-- the exported @LiftedSpec@, so a client that did not see it would get only
-- "the result is some fixed point of an uninterpreted symbol". @v ==
-- Data.Text.toLower v@ is IDEMPOTENCE, which is the one behavioural fact
-- assumed here.
--
-- There is deliberately no @tlen@ conjunct: full Unicode lowercasing can
-- LENGTHEN its input -- U+0130 lowercases to two code points -- so a
-- length-preservation claim would be false.
--
-- The @stringlen@ invariant is the counterpart of
-- @Data.ByteString_LHAssumptions@'s @bslen bs == stringlen bs@ rather than a
-- new idea. @Data.String_LHAssumptions@ gives an @IsString@ literal only
-- @len i == stringlen o@, so without it the logic knows the CHARACTER COUNT of
-- an @OverloadedStrings@ @Text@ literal and nothing at all about its @tlen@ --
-- which leaves @Data.Text.breakOn "}" t@ unprovable against the very
-- precondition stated below, at a literal needle that is visibly non-empty. It
-- is an equality rather than an inequality because @IsString Text@ is
-- @Data.Text.pack@ and @tlen@ is the code-point count both sides agree on.
{-@
measure tlen :: Text -> { n : Int | 0 <= n }

invariant { t : Text | 0 <= tlen t }

invariant { t : Text | tlen t == stringlen t }

measure tappend :: Text -> Text -> Text

measure tcons :: Char -> Text -> Text

assume Data.Text.null :: t : Text -> { b : Bool | b <=> tlen t == 0 }

assume Data.Text.length :: t : Text -> { n : Int | n == tlen t }

assume Data.Text.uncons :: t : Text
     -> { m : Maybe (Char, { r : Text | tlen r == tlen t - 1 }) | isJust m <=> 0 < tlen t }

assume Data.Text.span :: (Char -> Bool)
     -> t : Text
     -> (Text, { s : Text | tlen s <= tlen t })

assume Data.Text.breakOn :: { pat : Text | 0 < tlen pat }
     -> t : Text
     -> (Text, { s : Text | tlen s <= tlen t })

assume Data.Text.drop :: Int -> t : Text -> { s : Text | tlen s <= tlen t }

assume Data.Text.append :: a : Text
     -> b : Text
     -> { v : Text | tlen v == tlen a + tlen b && v == tappend a b }

assume Data.Text.cons :: c : Char
     -> t : Text
     -> { v : Text | tlen v == 1 + tlen t && v == tcons c t }

opaque-reflect Data.Text.toLower

assume Data.Text.toLower :: n : Text
     -> { v : Text | v == Data.Text.toLower n && v == Data.Text.toLower v }
@-}
