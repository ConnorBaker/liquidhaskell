{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fclear-plugins #-}

-- Deliberately compiled without LH: the client cannot rely on this module
-- carrying a transitive dependency on Prelude or any LH assumptions.
module TotalityExceptionFacade (throw, userError, error, errorWithoutStackTrace, undefined) where

import Control.Exception (throw)
import GHC.Err (error, errorWithoutStackTrace, undefined)
import System.IO.Error (userError)
