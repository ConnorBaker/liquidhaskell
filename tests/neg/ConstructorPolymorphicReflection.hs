module ConstructorPolymorphicReflection where



{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

data Box a = Box a

{-@ reflect makeBox @-}
makeBox :: Int -> Box Int
makeBox x = Box x

{-@ falseLaw :: x:Int -> {makeBox x == Box (x + 1)} @-}
falseLaw :: Int -> ()
falseLaw _ = ()
