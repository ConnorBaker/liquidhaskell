{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}

-- | The field-sort comparison has to skip GHC's DICTIONARY arguments before it
-- compares anything, and this module is the case where forgetting to is
-- visible.
--
-- @dataConRepArgTys@ leads with one argument per class constraint;
-- @dataConOrigArgTys@ carries none of them, and @dcpTyArgs@ keeps them in
-- @dcpTyConstrs@ instead. Comparing the two lists head-to-head therefore lines
-- the constructor's one FIELD up against its DICTIONARY, which are never the
-- same sort, so the field's selector is dropped, so nothing relates
-- @sel_1 VV@ to the constructor's argument, and the declaration is rejected:
--
--     Illegal type specification for `SomeTable`
--     Cannot unify Table with (Map row) ...
--
-- Aligning from the END fixes it, which is also how 'bkDataCon' numbered the
-- selector in the first place.
--
-- NOT an optimisation-level test, unlike its @UnpackedFieldBinders@ and
-- @UnpackedFieldSorts@ siblings, and that is worth knowing rather than an
-- accident: the misalignment is about dictionaries, not about unboxing, so it
-- does not wait for @-O1@. Measured @Illegal type specification@ at both @-O0@
-- and @-O1@ before the fix, and @SAFE (0 constraints checked)@ at @-O0@,
-- @-O1@ and @-O2@ after. It needs no @OPTIONS_GHC@ pragma to bite.
--
-- @Table@ must be a @data@ and not a @newtype@: a newtype is erased, the field
-- is already its own content, and nothing is unpacked. Measured -- the newtype
-- spelling of this module is @SAFE@ before the fix and proves nothing.
module ConstrainedFieldSorts where

class Rel row where
  relKey :: row -> Int

data Table row = Table ![(row, Int)]

data SomeTable where
  SomeTable :: (Rel row) => !(Table row) -> SomeTable
