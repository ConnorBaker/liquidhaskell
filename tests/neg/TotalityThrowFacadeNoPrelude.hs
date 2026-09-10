{-# LANGUAGE NoImplicitPrelude #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

module TotalityThrowFacadeNoPrelude (value) where

import GHC.Types (Int)
import TotalityExceptionFacade (throw, userError)

value :: Int
value = throw (userError "intentional")
