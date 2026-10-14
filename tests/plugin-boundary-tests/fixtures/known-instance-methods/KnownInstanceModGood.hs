module KnownInstanceModGood where

-- Int's Integral contract must admit the class contract's divisor domain
-- (`y == fromInteger 1` at the known Int dictionary).
modTwo :: Int -> Int
modTwo x = x `mod` 2
