module SelectorProducer (Box, produce) where

-- The abstract export keeps the constructor out of client Core, so a client
-- reads the field only through the producer's published datatype declaration.
data Box = Box Int

{-@ measure unbox :: Box -> Int
      unbox (Box value) = value
  @-}

{-@ produce :: value:Int -> {v:Box | unbox v == value} @-}
produce :: Int -> Box
produce value = Box value
