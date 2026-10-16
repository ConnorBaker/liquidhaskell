module SharedHoleTemplateFalse (scanAll) where

-- The bang on `st` lets case expansion copy scan's body, including the local
-- `continue` binding, into each constructor branch. Without an authored
-- result, `continue`'s checking template has an inferred result KVar that both
-- copies share. One copy calls `continue` without decreasing `input`.
data St = StA | StB

scanAll :: [Char] -> Int
scanAll = scan StA 0
 where
  {-@ scan :: St -> Int -> input:[Char] -> Int / [len input] @-}
  scan !st !n input =
    case input of
      [] -> (n :: Int)
      (c : rest) -> scanCharacter st c rest
   where
    {-@ continue :: St -> remaining:{t:[Char] | len t < len input} -> Int @-}
    continue st' remaining = scan st' n remaining
    scanCharacter StA '\n' remaining = continue StA remaining
    scanCharacter StA _ remaining = continue StB remaining
    scanCharacter StB _ _ = continue StA input
