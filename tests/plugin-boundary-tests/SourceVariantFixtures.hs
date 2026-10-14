module SourceVariantFixtures (copySourceFixture, sourceVariant) where

import CompilerFixture (copyFixture, writeFixture)
import Control.Monad ((>=>))
import Data.List (findIndices, isPrefixOf, tails)
import System.FilePath (replaceFileName)

-- Each counterexample is still compiled independently. Only the unchanged
-- source declarations are shared with its positive control.
copySourceFixture :: (FilePath -> IO FilePath) -> FilePath -> FilePath -> String -> IO ()
copySourceFixture fixture relative directory name =
    case sourceVariant name of
        Nothing -> copyFixture fixture relative directory name
        Just (original, change) -> do
            path <- fixture (replaceFileName relative (original ++ ".hs"))
            source <- readFile path
            either (ioError . userError) (writeFixture relative directory name) (change source)

sourceVariant :: String -> Maybe (String, String -> Either String String)
sourceVariant name = do
    change <- lookup name variants
    let original = take (length name - 3) name ++ "Good"
    pure (original, change >=> replaceOnce ("module " ++ original ++ " ") ("module " ++ name ++ " "))

-- These are ordinary Haskell source transformations. The changed declarations
-- and implementations remain explicit; no failure is shared between cases.
variants :: [(String, String -> Either String String)]
variants =
    [
        ( "AliasDomainBad"
        , replaceOnce "use = restricted True\n" "use = restricted False\n"
        )
    ,
        ( "ForeignAssumptionBad"
        , replaceOnce "{-@ assume ord :: Char -> {v:Int | 0 <= positive 1} @-}\n" "{-@ assume ord :: Char -> {v:Int | 0 <= positive 0} @-}\n"
        )
    ,
        ( "ProjectionIncompleteBad"
        , replaceOnce "{-@ missing :: n:Int -> {v:Bool | selected Empty == n => v} @-}\n" "{-@ missing :: n:Int -> {v:Bool | selected Empty == n} @-}\n"
        )
    ,
        ( "ObligationContextBad"
        , replaceOnce "probe = requiresPositive 1\n" "probe = requiresPositive 0\n"
        )
    ,
        ( "TelescopeContextBad"
        , replaceOnce "{-@ probe :: forall a <p :: a -> Bool>. b:{v:Bool | v} -> (x:a<p> -> {v:a | b => v == x}) -> a<p> -> a<p> @-}\n" "{-@ probe :: forall a <p :: a -> Bool>. b:Bool -> (x:a<p> -> {v:a | b => v == x}) -> a<p> -> a<p> @-}\n"
        )
    ,
        ( "ExistentialMeasureBad"
        , replaceOnce "{-@ good :: {v:Bool | v} @-}\ngood :: Bool\ngood = packageTag (Package True (id :: Bool -> Bool))\n" "{-@ bad :: {v:Bool | v} @-}\nbad :: Bool\nbad = packageTag (Package False (id :: Bool -> Bool))\n"
        )
    ,
        ( "ExistentialSelectorBad"
        , replaceOnce "{-@ good :: {v:Bool | v} @-}\ngood :: Bool\ngood = case Package True (id :: Bool -> Bool) of\n" "{-@ bad :: {v:Bool | v} @-}\nbad :: Bool\nbad = case Package False (id :: Bool -> Bool) of\n"
        )
    ,
        ( "VectorDefaultHeightBad"
        , replaceOnce "visit (Branch children) = Vector.foldr (\\child rest -> visit child `seq` rest) () children\n" "visit tree@(Branch children) = Vector.foldr (\\_ rest -> visit tree `seq` rest) () children\n"
        )
    ,
        ( "DefaultStimesBad"
        , replaceOnce "module DefaultStimesGood where\n" "module DefaultStimesGood where\n\nimport Data.Semigroup (stimes)\n"
            >=> replaceOnce "    _ <> right = right\n" "    _ <> right = right\n\nuse :: Box\nuse = stimes (1 :: Int) (Box False)\n"
        )
    ,
        ( "StagedMeasureCycleBad"
        , replaceOnce "{-@ rightMeasure :: input:Bool -> {value:Integer | value == leftMeasure input} @-}\n" "{-@ rightMeasure :: input:Bool -> {value:Integer | value == leftMeasure input + 1} @-}\n"
        )
    ,
        ( "FunctionCoercionBad"
        , replaceOnce "{-@ transport :: (Nat -> a) -> Nat -> b @-}\n" "{-@ transport :: (Nat -> a) -> Int -> b @-}\n"
        )
    ,
        ( "HigherKindedCallbackBad"
        , replaceOnce "good :: Bool\ngood = invoke (Box 1) positive\n" "bad :: Bool\nbad = invoke (Box 0) positive\n"
        )
    ,
        ( "IgnoredNestedBad"
        , replaceOnce "{-@ ordinary :: {v:Integer | v == 0} @-}\n" "{-@ ordinary :: {v:Integer | v == 1} @-}\n"
        )
    ,
        ( "LocalColonBad"
        , replaceOnce "    {-@ (.:) :: left:Bool -> Bool -> {result:Bool | result == left} @-}\n" "    {-@ (.:) :: Bool -> right:Bool -> {result:Bool | result == right} @-}\n"
        )
    ,
        ( "OwnedHelperBad"
        , replaceOnce "{-@ ownedNested :: value:Bool -> {result:Bool | result == value} @-}\n" "{-@ ownedNested :: value:Bool -> {result:Bool | result /= value} @-}\n"
        )
    ,
        ( "OwnedIdentityBad"
        , replaceOnce "{-@ ownedIdentity :: value:Bool -> {result:Bool | result == value} @-}\n" "{-@ ownedIdentity :: value:Bool -> {result:Bool | result /= value} @-}\n"
        )
    ,
        ( "OwnedOperatorBad"
        , replaceOnce "{-@ (A..:) :: left:Bool -> Bool -> {result:Bool | result == left} @-}\n" "{-@ (A..:) :: Bool -> right:Bool -> {result:Bool | result == right} @-}\n"
        )
    ,
        ( "CheckedCarrierBad"
        , replaceOnce "good :: Int\ngood = generic 1\n" "bad :: Int\nbad = generic 0\n"
        )
    ,
        ( "EqualityInstanceBad"
        , replaceOnce "{-@ identityString :: input:[Char] -> {output:[Char] | output == input} @-}\n" "{-@ identityString :: input:[Char] -> {output:[Char] | output /= input} @-}\n"
        )
    ,
        ( "ImportedInstanceQueryOnlyBad"
        , replaceOnce "queryOnly x = x\n" "queryOnly _ = 0\n"
        )
    ,
        ( "OwnedInstanceBad"
        , replaceOnce "      pick :: x:Int -> {v:Int | v == x} @-}\n" "      pick :: x:{v:Int | v > 0} -> {v:Int | v == x} @-}\n"
        )
    ,
        ( "InstanceFormationBad"
        , replaceOnce "      check :: Token -> flag:Bool -> {value:Integer | flag => onlyTrue flag == onlyTrue flag}\n" "      check :: Token -> flag:Bool -> {value:Integer | onlyTrue flag == onlyTrue flag}\n"
        )
    ,
        ( "InstancePlainCarrierBad"
        , replaceOnce "good :: Int\ngood = generic 1\n" "bad :: Int\nbad = generic 0\n"
        )
    ,
        ( "LexicalBranchTautologyBad"
        , replaceOnce "        then\n" "        then False\n        else\n"
            >=> replaceOnce "        else False\n" ""
        )
    ,
        ( "LexicalCallbackBad"
        , replaceOnce "{-@ outer :: k:(x:{Bool | x} -> {v:Bool | v}) -> b:{Bool | b} -> Bool @-}\n" "{-@ outer :: k:(x:{Bool | x} -> {v:Bool | v}) -> b:Bool -> Bool @-}\n"
        )
    ,
        ( "LexicalShadowTautologyBad"
        , replaceOnce "{-@ outer :: b:Bool -> Bool @-}\n" "{-@ outer :: b:{Bool | b} -> Bool @-}\n"
            >=> replaceOnce "outer b = if b then local True else local True\n" "outer b = if b then local False else local False\n"
            >=> replaceOnce "    {-@ local :: b:{Bool | b} -> Bool @-}\n" "    {-@ local :: b:Bool -> Bool @-}\n"
        )
    ,
        ( "ConstrainedMethodDomainBad"
        , replaceOnce "use = selected True True True\n" "use = selected True False True\n"
        )
    ,
        ( "RecursiveMethodRecordBad"
        , replaceOnce "walk (More child) = generic (Method walk) child\n" "walk current@(More _) = generic (Method walk) current\n"
        )
    ,
        ( "CallbackBoxBad"
        , replaceOnce "{-@ consume :: {h:Box (b:{Bool | b} -> Bool) | unBox h True} -> Bool @-}\n" "{-@ consume :: {h:Box (b:{Bool | b} -> Bool) | unBox h False} -> Bool @-}\n"
        )
    ,
        ( "CallbackRootBad"
        , replaceOnce "{-@ consume :: {g:(b:{Bool | b} -> Bool) | g True} -> Bool @-}\n" "{-@ consume :: {g:(b:{Bool | b} -> Bool) | g False} -> Bool @-}\n"
        )
    ,
        ( "SetCardinalityBad"
        , replaceOnce "size = Set.size\n" "size _ = 0\n"
        )
    ,
        ( "SetCompositionBad"
        , replaceOnce "isEmpty = Set.null . id\n" "isEmpty = not . Set.null\n"
        )
    ,
        ( "ByteStringWord8ModelBad"
        , replaceOnce "-- This owned model uses Word8's numeric interpretation. The imported opaque\n-- unpack observation must publish the same list-element sort, without a local\n-- restatement or cast of that observation.\n" ""
            >=> replaceOnce "{-@ observedModel :: bytes:ByteString\n" "-- Empty output cannot conserve the actual observation of a nonempty input.\n-- This tests an incorrect owned implementation, not an assume projection.\n{-@ observedModel :: bytes:{ByteString | 0 < bslen bytes}\n"
            >=> replaceOnce "observedModel bytes = byteModel (ByteString.unpack bytes)\n" "observedModel _bytes = []\n"
        )
    ,
        ( "FamilyRootBad"
        , replaceOnce "positive = I# 1#\n" "positive = I# 0#\n"
        )
    ]

replaceOnce :: String -> String -> String -> Either String String
replaceOnce before after source =
    case findIndices (isPrefixOf before) (tails source) of
        [offset]
            | not (null before) ->
                Right (take offset source ++ after ++ drop (offset + length before) source)
        offsets ->
            Left ("fixture variant requires one occurrence of " ++ show before ++ "; found " ++ show (length offsets))
