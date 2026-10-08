{-@ LIQUID "--ple" @-}
module MapCompositionLaws where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

{-@ opaque-reflect tableUnionRows @-}
tableUnionRows :: Map Integer (Set Integer) -> Map Integer (Set Integer) -> Map Integer (Set Integer)
tableUnionRows = Map.unionWith Set.union

{-@ opaque-reflect lookupRows @-}
lookupRows :: Map Integer (Set Integer) -> Integer -> Maybe (Set Integer)
lookupRows m k = Map.lookup k m

{-@ reflect maybeUnion @-}
maybeUnion :: Maybe (Set Integer) -> Maybe (Set Integer) -> Maybe (Set Integer)
maybeUnion Nothing Nothing = Nothing
maybeUnion Nothing (Just y) = Just y
maybeUnion (Just x) Nothing = Just x
maybeUnion (Just x) (Just y) = Just (Set.union x y)

{-@ maybeIdem :: x:Maybe (Set Integer) -> {v:Maybe (Set Integer) | v == x && v == maybeUnion x x} @-}
maybeIdem :: Maybe (Set Integer) -> Maybe (Set Integer)
maybeIdem Nothing = Nothing
maybeIdem (Just x) = Just (Set.union x x)

{-@ maybeComm :: x:Maybe (Set Integer) -> y:Maybe (Set Integer) -> {u:() | maybeUnion x y == maybeUnion y x} @-}
maybeComm :: Maybe (Set Integer) -> Maybe (Set Integer) -> ()
maybeComm Nothing Nothing = ()
maybeComm Nothing (Just _) = ()
maybeComm (Just _) Nothing = ()
maybeComm (Just _) (Just _) = ()

{-@ assume unionLookup :: a:Map Integer (Set Integer) -> b:Map Integer (Set Integer) -> k:Integer -> {u:() | lookupRows (tableUnionRows a b) k == maybeUnion (lookupRows a k) (lookupRows b k)} @-}
unionLookup :: Map Integer (Set Integer) -> Map Integer (Set Integer) -> Integer -> ()
unionLookup _ _ _ = ()

{-@ assume mapExt :: a:Map Integer (Set Integer) -> b:Map Integer (Set Integer) -> (k:Integer -> {u:() | lookupRows a k == lookupRows b k}) -> {u:() | a == b} @-}
mapExt :: Map Integer (Set Integer) -> Map Integer (Set Integer) -> (Integer -> ()) -> ()
mapExt _ _ _ = ()

{-@ unionComm :: a:Map Integer (Set Integer) -> b:Map Integer (Set Integer) -> {u:() | tableUnionRows a b == tableUnionRows b a} @-}
unionComm :: Map Integer (Set Integer) -> Map Integer (Set Integer) -> ()
unionComm a b =
    mapExt
        (tableUnionRows a b)
        (tableUnionRows b a)
        ( \k -> case unionLookup a b k of
            () -> case unionLookup b a k of
                () -> maybeComm (lookupRows a k) (lookupRows b k)
        )

{-@ unionIdem :: a:Map Integer (Set Integer) -> {u:() | tableUnionRows a a == a} @-}
unionIdem :: Map Integer (Set Integer) -> ()
unionIdem a =
    mapExt
        (tableUnionRows a a)
        a
        ( \k -> case maybeIdem (lookupRows a k) of
            Nothing -> unionLookup a a k
            Just _ -> unionLookup a a k
        )
