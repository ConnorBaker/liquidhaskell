{-# OPTIONS_GHC -O1 #-}

-- | A measure whose body takes an UNPACKed constructor apart with a nested
-- @case@.
--
-- 'unpackedFieldSubst' rewrites the binders of a lifted equation's OWN
-- top-level alternative. A @case@ INSIDE the body is lifted by 'altToLg', which
-- had the same defect and did not get the same fix: it zips the alternative's
-- binders against @makeDataConSelector d i@ for @i = 1..@, but those binders
-- are @d@'s REPRESENTATION arguments while the selectors name its SOURCE
-- fields. The two lists correspond only while GHC has unpacked nothing.
--
-- Here @P@'s single source field is an @{-# UNPACK #-}@ed two-field product, so
-- the alternative @P q@ binds TWO @Int#@s where the logic's @P@ has one field.
-- Before the fix the projection is built against the wrong list and the
-- declaration is rejected with @Illegal type specification@.
--
-- Three properties of this shape are load bearing, and the first two were each
-- established by an arm that pinned NOTHING:
--
-- * The nested case's own constructor must be the one with the unpacked field.
--   A first attempt put the @{-# UNPACK #-}@ one level out -- @Boxed !Pair@,
--   with the inner case on @Pair@ -- and measured @SAFE (1)@ with the fix
--   disarmed. @Pair@'s own fields are not unpacked, so its representation
--   arguments and source fields already correspond and 'altToLg' has nothing to
--   repair; the unpacking was INTO @Boxed@, which is 'unpackedFieldSubst''s
--   business, not this one's.
--
-- * @Outer@'s field is LAZY. Unpacked, the outer equation's own alternative is
--   rewritten by 'unpackedFieldSubst' and the module fails there first.
--
-- * @P2@ has TWO fields of the SAME embedded sort, so no field of @P@ resorts
--   and the projection can actually be built. A single-field wrapper always
--   resorts -- the wrapper's sort is not its field's -- which reaches the
--   refusal branch instead. That is the companion negative,
--   @tests/datacon/neg/NestedCaseProjectionSort.hs@.
module NestedCaseProjection where

data P2 = P2 !Int !Int

data P = P {-# UNPACK #-} !P2

data Outer = Outer P

{-@ measure outerP2 @-}
outerP2 :: Outer -> P2
outerP2 (Outer p) = case p of P q -> q

{-@ mk :: q:P2 -> {v:Outer | outerP2 v == q} @-}
mk :: P2 -> Outer
mk q = Outer (P q)
