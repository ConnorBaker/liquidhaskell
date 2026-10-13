module SourceAliasEmbeddingWrong where

data Evidence = Evidence Integer
type Alias = Evidence

{-@ embed Evidence as int @-}
{-@ embed Alias as bool @-}

identityAlias :: Alias -> Evidence
identityAlias x = x
