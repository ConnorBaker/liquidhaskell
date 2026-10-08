module ConstrainedMethodDomainUnknown where

class Extra a where
    extra :: a -> Bool
    extraTag :: a -> Bool

instance Extra Bool where
    extra value = value
    extraTag _ = True

class Source a where
    {-@ selected :: forall b. Extra b => a -> {flag:Bool | flag} -> b -> Bool @-}
    selected :: (Extra b) => a -> Bool -> b -> Bool
    sourceTag :: a -> Bool

instance Source Bool where
    selected _ flag _ = flag
    sourceTag _ = True

use :: (Source a, Extra b) => a -> b -> Bool
use source extraValue = selected source False extraValue
