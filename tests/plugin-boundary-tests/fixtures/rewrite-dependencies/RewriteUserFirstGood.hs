{-@ LIQUID "--rw-termination-check" @-}
module RewriteUserFirstGood where

import Prelude hiding ((++))

{-@ infix ++ @-}

-- `four` uses `assoc` only as a rewrite rule, never through a Core call, and
-- precedes it in the source. The theorem must still be established first.
{-@ four :: xs:[a] -> ys:[a] -> zs:[a] -> ws:[a]
         -> {xs ++ (ys ++ (zs ++ ws)) == ((xs ++ ys) ++ zs) ++ ws} @-}
four :: [a] -> [a] -> [a] -> [a] -> ()
four _ _ _ _ = ()

{-@ rewrite assoc @-}
{-@ assoc :: xs:[a] -> ys:[a] -> zs:[a] -> {xs ++ (ys ++ zs) == (xs ++ ys) ++ zs} @-}
assoc :: [a] -> [a] -> [a] -> ()
assoc [] _ _ = ()
assoc (_ : xs) ys zs = assoc xs ys zs

{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x : xs) ++ ys = x : (xs ++ ys)
