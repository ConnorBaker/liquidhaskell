module ImportedConstructors (T (..), Packed (..)) where

data T = A | B {-# UNPACK #-} !Int

data Packed a = Packed {-# UNPACK #-} !Int a
