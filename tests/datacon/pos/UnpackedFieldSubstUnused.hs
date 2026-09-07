{-# OPTIONS_GHC -O1 #-}

-- | A constructor carrying a field that has NO selector -- @W@ wraps a @Set@,
-- so unpacking rewrites its sort -- beside one that does, and an equation that
-- projects only through the second.
--
-- Neither 'CoreToLogic.altToLg' nor its twin at 'unpackedFieldSubst' may refuse
-- here, and the obvious spelling of the refusal does. Deciding it from the
-- CONSTRUCTOR -- "does @C@ have a resorted field" -- is measured wrong: it
-- turned ELEVEN passing modules in this directory red on 2026-09-06, among them
-- the five @Dep@ ones, which project field 1 while field 2 is the @Set@ that
-- resorts. So the question is asked of the EMITTED equation instead, after
-- 'etaCollapse': does it actually NAME a selector nobody declared.
--
-- Here it does not. The alternative's binders reach @q@ through @C@'s SECOND
-- selector, and the @P2@ reconstruction collapses back to exactly that.
--
-- @mkA2@ is load bearing and its absence costs nothing visible: with no
-- consumer the measure raises no obligation and the module is
-- @SAFE (0 constraints checked)@, which reads like a clean result and proves
-- nothing. With it the module is @SAFE (1)@.
module UnpackedFieldSubstUnused where

import Data.Set (Set)

data W = W (Set Int)

data P2 = P2 !Int !Int

data C = C !W {-# UNPACK #-} !P2

data A2 = A2 C

{-@ measure a2P @-}
a2P :: A2 -> P2
a2P (A2 c) = case c of C _ q -> q

{-@ mkA2 :: w:W -> q:P2 -> {v:A2 | a2P v == q} @-}
mkA2 :: W -> P2 -> A2
mkA2 w q = A2 (C w q)
