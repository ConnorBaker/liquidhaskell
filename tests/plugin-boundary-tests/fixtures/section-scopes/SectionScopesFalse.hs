module SectionScopesFalse where

-- Both sections bind GHC's template local v_B3, to 1 and to 2. Floated into
-- one let chain, both bindings' facts would contradict each other and prove
-- the false result below.

applyAll :: [Int -> Int] -> Int -> Int
applyAll [] _ = 0
applyAll (f : fs) n = f n + applyAll fs n

{-@ total :: Int -> {v:Int | false} @-}
total :: Int -> Int
total n = applyAll [(+ 1), (+ 2)] n
