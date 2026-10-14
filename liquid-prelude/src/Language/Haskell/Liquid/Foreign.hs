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

{-# NOINLINE intCSize #-}
{-@ assume intCSize :: x:Int -> {v: CSize | v = x } @-}
intCSize :: Int -> CSize
intCSize = fromIntegral

-- CSize has no instance contracts of its own. Convert through its Word64
-- representation, whose contracts exist; the Int conversion is exact only
-- below 2^63, so that range is a checked premise rather than an assumption.
{-# NOINLINE cSizeInt #-}
{-@ cSizeInt :: x:{CSize | x < 9223372036854775808} -> {v: Int | v = x } @-}
cSizeInt :: CSize -> Int
cSizeInt (CSize w) = fromInteger (toInteger w)


{-@ assume mkPtr :: x:Addr# -> {v: (Ptr b) | ((plen v) = (addrLen x) && ((plen v) >= 0)) } @-}
mkPtr   :: Addr# -> Ptr b
mkPtr = undefined -- Ptr x


{-@ assume isNullPtr :: p:(Ptr a) -> {v:Bool | (v <=> (isNullPtr p)) } @-}
isNullPtr :: Ptr a -> Bool
isNullPtr p = (p == nullPtr)
{-# INLINE isNullPtr #-}

{-@ fpLen :: p:(ForeignPtr a) -> {v:Int | v = (fplen p) } @-}
fpLen :: ForeignPtr a -> Int
fpLen = undefined

{-@ pLen :: p:(Ptr a) -> {v:Int | v = (plen p) } @-}
pLen :: Ptr a -> Int
pLen = undefined

{-@ deref :: p:Ptr a -> {v:a | v = (deref p)} @-}
deref :: Ptr a -> a
deref = undefined

{-@ eqPtr :: p:PtrV a
          -> q:{v:PtrV a | (((pbase v) = (pbase p)) && ((plen v) <= (plen p)))}
          -> {v:Bool | (v <=> ((plen p) = (plen q)))}
  @-}
eqPtr :: Ptr a -> Ptr a -> Bool
eqPtr = undefined
