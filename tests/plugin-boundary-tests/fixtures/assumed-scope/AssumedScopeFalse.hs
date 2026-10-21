{-# LANGUAGE DerivingVia #-}
module AssumedScopeFalse (Req (..), Batch (..), Res (..), BRes (..), ToJ (..), encodedEmpty) where

-- The unsigned schemaVersion couples both versioned codecs (and their
-- dictionaries) into one proof group. BRes's codec, solved there, can state
-- facts about Req's codec, which BRes's ToJ method does not reach: a query
-- assuming that solved type must still declare Req's codec.

import qualified Data.Set as Set

data Fields v = Fields (Set.Set String) (v -> [Int])

{-@ measure fieldNames @-}
fieldNames :: Fields v -> Set.Set String
fieldNames (Fields names _) = names

data Codec v = Codec String (Fields v)

class HasCodec v where
  codecFor :: Codec v

class ToJ a where
  toJ :: a -> [Int]

instance ToJ a => ToJ [a] where
  toJ = concatMap toJ

newtype Via v = Via v

instance HasCodec v => ToJ (Via v) where
  toJ (Via value) = case codecFor of Codec _ (Fields _ encode) -> encode value

field :: String -> (v -> Int) -> Fields v
field name project = Fields (Set.singleton name) (\value -> [project value])

{-@ versioned :: String -> Int -> (v -> payload) -> Codec v @-}
versioned :: ToJ payload => String -> Int -> (v -> payload) -> Codec v
versioned label version project =
  Codec label (Fields (Set.fromList ["schemaVersion", "payload"]) (\value -> version : toJ (project value)))

schemaVersion :: Int
schemaVersion = 1

data Req = Req Int
  deriving (ToJ) via (Via Req)

instance HasCodec Req where
  codecFor = Codec "Req" (field "id" (\(Req n) -> n))

newtype Batch = Batch [Req]
  deriving (ToJ) via (Via Batch)

instance HasCodec Batch where
  codecFor = versioned "Batch" schemaVersion (\(Batch requests) -> requests)

data Res = Res Int
  deriving (ToJ) via (Via Res)

instance HasCodec Res where
  codecFor = Codec "Res" (field "id" (\(Res n) -> n))

newtype BRes = BRes [Res]
  deriving (ToJ) via (Via BRes)

instance HasCodec BRes where
  codecFor = versioned "BRes" schemaVersion (\(BRes results) -> results)

{-@ encodedEmpty :: BRes -> {v:[Int] | len v == 0} @-}
encodedEmpty :: BRes -> [Int]
encodedEmpty = toJ
