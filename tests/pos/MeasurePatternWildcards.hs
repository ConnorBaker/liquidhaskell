{-@ LIQUID "--total-Haskell" @-}
module MeasurePatternWildcards where

data Pair = Pair Int Int

-- Ignoring two fields must not identify them in other measures' equations.
{-@ measure repeated :: Pair -> Bool
      repeated (Pair _ _) = true
  @-}
{-@ measure first :: Pair -> Int
      first (Pair left right) = left
  @-}
{-@ measure second :: Pair -> Int
      second (Pair left right) = right
  @-}
{-@ measure hostile :: Pair -> Int
      hostile (Pair _ lq_tmp$measureWildcard##1) = lq_tmp$measureWildcard##1
  @-}

{-@ correctFact :: Int -> {v:Pair | first v == 0 && second v == 1 && hostile v == 1} @-}
correctFact :: Int -> Pair
correctFact _ = Pair 0 1

{-@ fail wrongFact @-}
{-@ wrongFact :: Int -> {v:Pair | first v == 1 && second v == 1} @-}
wrongFact :: Int -> Pair
wrongFact _ = Pair 0 1

{-@ fail wrongEquality @-}
{-@ wrongEquality :: Pair -> {v:Bool | v} @-}
wrongEquality :: Pair -> Bool
wrongEquality (Pair left right) = left == right

{-@ measure tupleWild :: (a,b) -> Bool
      tupleWild (_,_) = true
  @-}
{-@ tupleFact :: Int -> {v:(Int,Int) | tupleWild v} @-}
tupleFact :: Int -> (Int,Int)
tupleFact x = (x, x + 1)

{-@ measure listWild :: [a] -> Bool
      listWild [] = true
      listWild (_ : _) = true
  @-}
{-@ listFact :: Int -> {v:[Int] | listWild v} @-}
listFact :: Int -> [Int]
listFact x = [x]

{-@ class measure marked :: forall a. a -> Bool @-}
{-@ instance measure marked :: Pair -> Bool
      marked (Pair _ _) = true
  @-}
{-@ markedFact :: Int -> {v:Pair | marked v} @-}
markedFact :: Int -> Pair
markedFact x = Pair x (x + 1)

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | v > 0} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe x = x - 1
