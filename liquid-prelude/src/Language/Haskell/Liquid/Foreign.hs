{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# LANGUAGE MagicHash #-}

{- OPTIONS_GHC -cpp #-}
{- OPTIONS_GHC -cpp -fglasgow-exts -}

module Language.Haskell.Liquid.Foreign where

import Foreign.C.Types          (CSize(..))
import Foreign.Ptr
import Foreign.ForeignPtr
import GHC.Base

import Data.Word (Word64) -- Necessary to bring in scope the evidence that Word64 = int

-- TODO: shouldn't have to re-import these (tests/pos/imp0.hs)
{- import Foreign.C.Types    -}
{- import Foreign.Ptr        -}
{- import Foreign.ForeignPtr -}
{- import GHC.Base           -}



-----------------------------------------------------------------------------------------------

-- Word64's conversion from Integer wraps, so the Int-to-CSize conversion is
-- exact only for nonnegative arguments; callers prove that premise.
{-# NOINLINE intCSize #-}
{-@ intCSize :: x:{Int | 0 <= x} -> {v: CSize | v = x } @-}
intCSize :: Int -> CSize
intCSize x = CSize (fromInteger (toInteger x))

-- CSize has no instance contracts of its own. Convert through its Word64
-- representation, whose contracts exist; the Int conversion is exact only
-- below 2^63, so that range is a checked premise rather than an assumption.
{-# NOINLINE cSizeInt #-}
{-@ cSizeInt :: x:{CSize | x < 9223372036854775808} -> {v: Int | v = x } @-}
cSizeInt :: CSize -> Int
cSizeInt (CSize w) = fromInteger (toInteger w)


-- These stubs name logical observations; every call diverges (undefined).
-- Their checked domain is therefore unreachable, as for liquidError.
{-@ mkPtr :: x:{x:Addr# | false} -> {v: (Ptr b) | ((plen v) = (addrLen x) && ((plen v) >= 0)) } @-}
mkPtr   :: Addr# -> Ptr b
mkPtr _ = undefined -- Ptr x


{-@ assume isNullPtr :: p:(Ptr a) -> {v:Bool | (v <=> (isNullPtr p)) } @-}
isNullPtr :: Ptr a -> Bool
isNullPtr p = (p == nullPtr)
{-# INLINE isNullPtr #-}

{-@ fpLen :: p:{p:ForeignPtr a | false} -> {v:Int | v = (fplen p) } @-}
fpLen :: ForeignPtr a -> Int
fpLen _ = undefined

{-@ pLen :: p:{p:Ptr a | false} -> {v:Int | v = (plen p) } @-}
pLen :: Ptr a -> Int
pLen _ = undefined

{-@ deref :: p:{p:Ptr a | false} -> {v:a | v = (deref p)} @-}
deref :: Ptr a -> a
deref _ = undefined

{-@ eqPtr :: p:{p:PtrV a | false}
          -> q:{v:PtrV a | (((pbase v) = (pbase p)) && ((plen v) <= (plen p)))}
          -> {v:Bool | (v <=> ((plen p) = (plen q)))}
  @-}
eqPtr :: Ptr a -> Ptr a -> Bool
eqPtr _ _ = undefined
