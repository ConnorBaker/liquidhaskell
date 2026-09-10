{-# OPTIONS_GHC -O1 #-}

-- | A strict field whose type EMBEDS and whose unboxed component does not.
--
-- @Word8@ embeds to @int@ (@GHC.Word_LHAssumptions@), and from @-O1@ up
-- @-funbox-small-strict-fields@ replaces a @!Word8@ field by the @Word8#@
-- inside it, which embeds to nothing: @GHC.Types_LHAssumptions@ embeds
-- @Int#@, @Word#@, @Word64#@, @Double#@, @Float#@, @Char#@, @Addr#@ and
-- @ByteArray#@, and of the sized @IntN#@/@WordN#@ primitives only @Word64#@.
-- So the field's ONE worker argument sits at a sort other than the one its own
-- type embeds to. The same holds for @Word16@, @Word32@, @Int8@, @Int16@,
-- @Int32@ and @Int64@ -- @Int64#@ is word-sized and equally unembedded, so
-- this is not about width; @Word64@ is the control, since @Word64#@ IS
-- embedded and nothing moves.
--
-- 'ElfSymbol' is the shape this was found on, verbatim from a downstream
-- module: a @Word8@ beside an @Int@ and two @Integer@s, with NO specification
-- at all. Against the RepMap series it was rejected at its own declaration at
-- @-O2@ with @Illegal type specification for `ElfSymbol`@ and
-- @Cannot unify int with GHC.Internal.Prim.Word8# in expression:
-- ElfSymbol##lqdc##$select##ElfSymbol##1 VV == lqdc##$select##ElfSymbol##1##ElfSymbol@,
-- while the series base (3a9bcadd, "Keep an unpacked field's refinement, in
-- both expansion branches") accepted it, @SAFE (0 constraints checked)@.
--
-- The RepMap's 'fieldRebuildable' answered 'True' for such a field: its shape
-- is an 'Atom' with no newtype chain, so the rebuild of the field from its one
-- worker argument is that argument itself, and there is no constructor whose
-- absence from the logic could make it inexpressible. But the field's
-- selector is declared at the field's SOURCE type, @int@, and the argument is
-- a @Word8#@, so @sel (D y) = y@ is not well sorted, and the constructor's
-- result refinement @sel VV == y@ was rejected. The series base dropped the
-- selector of EVERY field whose sort moved and so never emitted the equation.
-- Now 'frLeafResorted' records that the argument's sort differs from that of
-- the type it stands for, 'fieldRebuildable' is 'False' for it, and the
-- selector is dropped again. The measurement is per type, at @-O2@, against
-- the series tip and the series base: @Word8@, @Word16@, @Word32@, @Int8@,
-- @Int16@, @Int32@, @Int64@ each @Illegal type specification@ / @SAFE (1)@;
-- @Word64@ @SAFE (1)@ / @SAFE (1)@.
--
-- The companion negative is @tests/datacon/neg/UnpackedFieldSubWord.hs@: the
-- same record with a claim the measure equation contradicts, so that the
-- @SAFE@ here is a proof about 'tN' and not a vacuous environment.
module UnpackedFieldSubWord where

import Data.Int (Int16, Int32, Int64, Int8)
import Data.Word (Word16, Word32, Word64, Word8)

-- | One ELF64 symbol-table entry, as the downstream module declares it.
data ElfSymbol = ElfSymbol
  { elfSymbolInfo :: !Word8
  , elfSymbolSectionIndex :: !Int
  , elfSymbolValue :: !Integer
  , elfSymbolSize :: !Integer
  }
  deriving (Eq, Show)

data T = T
  { t8  :: !Word8
  , t16 :: !Word16
  , t32 :: !Word32
  , t64 :: !Word64
  , i8  :: !Int8
  , i16 :: !Int16
  , i32 :: !Int32
  , i64 :: !Int64
  , tN  :: !Int
  }

{-@ measure tN @-}

{-@ mk :: Word8 -> Word16 -> Word32 -> Word64 -> Int8 -> Int16 -> Int32 -> Int64 -> n:Int -> {v:T | tN v == n} @-}
mk :: Word8 -> Word16 -> Word32 -> Word64 -> Int8 -> Int16 -> Int32 -> Int64 -> Int -> T
mk = T

-- The same claim through a constructor APPLICATION rather than an eta-reduced
-- reference to the wrapper, so the worker's own spec is exercised.
{-@ mkApp :: Word8 -> n:Int -> {v:T | tN v == n} @-}
mkApp :: Word8 -> Int -> T
mkApp w n = T w 0 0 0 0 0 0 0 n
