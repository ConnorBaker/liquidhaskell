module RecursiveMethodRecordBad where

data Input = Stop | More Input

{-@ autosize Input @-}

data Method a = Method (a -> Bool)

generic :: Method a -> a -> Bool
{-@ generic :: Method a -> a -> Bool @-}
generic (Method method) value = method value

walk :: Input -> Bool
{-@ walk :: Input -> Bool @-}
walk Stop = False
walk current@(More _) = generic (Method walk) current
