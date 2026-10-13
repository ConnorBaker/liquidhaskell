module SourceAliasEmbeddingGood where

data Evidence = Evidence Integer
type Alias = Evidence

{-@ embed Evidence as int @-}
{-@ embed Alias as int @-}

{-@ identityAlias :: Alias -> Evidence @-}
identityAlias :: Alias -> Evidence
identityAlias x = x
