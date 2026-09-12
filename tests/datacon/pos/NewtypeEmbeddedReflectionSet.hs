{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module NewtypeEmbeddedReflectionSet (Support, wrap, unwrap, unionSupport, unionIdempotent, forceUnion) where
import Data.Coerce (coerce)
import Data.Set qualified as Set

{-@ embed Support as (Set_Set int) @-}
newtype Support = Support (Set.Set Int)

{-@ wrap :: entries:Set.Set Int -> {v:Support | v == entries} @-}
wrap :: Set.Set Int -> Support
wrap = Support

{-@ unwrap :: support:Support -> {v:Set.Set Int | v == support} @-}
unwrap :: Support -> Set.Set Int
unwrap = coerce

{-@ reflect unionSupport @-}
{-@ unionSupport :: left:Support -> right:Support -> {v:Support | v == Set_cup left right} @-}
unionSupport :: Support -> Support -> Support
unionSupport left right = wrap (Set.union (unwrap left) (unwrap right))

{-@ unionIdempotent :: support:Support -> {v:Support | v == support && v == unionSupport support support} @-}
unionIdempotent :: Support -> Support
unionIdempotent support = unionSupport support support

{-@ forceUnion :: support:Support -> {unionSupport support support == support} @-}
forceUnion :: Support -> ()
forceUnion support = unionSupport support support `seq` ()

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
