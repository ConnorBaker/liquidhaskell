module IdentityFixture (payloadType) where

import Data.Proxy (Proxy (..))
import Data.Typeable (TypeRep, typeRep)

data Payload = Payload

payloadType :: TypeRep
payloadType = typeRep (Proxy :: Proxy Payload)
