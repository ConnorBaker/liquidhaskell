{-# LANGUAGE ViewPatterns #-}

import           Control.Monad
import           Control.Monad.IO.Class (liftIO)
import           Data.List (find, isPrefixOf)
import           Data.Time (getCurrentTime)
import           Liquid.GHC.API
    ( ApiComment(ApiBlockComment)
    , Expr(..)
    , Alt(..)
    , AltCon(..)
    , LitNumType(..)
    , Literal(..)
    , apiCommentsParsedSource
    , InstDecl(ClsInstD)
    , hsGroupInstDecls
    , occNameString
    , pAT_ERROR_ID
    , showPprQualified
    , splitDollarApp
    , tcg_rn_decls
    , untick
    )
import           Liquid.GHC.API.Extra (addNoInlinePragmasToBinds)
import           Language.Haskell.Liquid.Transforms.Rewrite (rewriteBinds)
import qualified Language.Haskell.Liquid.Types.RefType as RefType
import           Language.Haskell.Liquid.Types.RType (SpecType)
import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.UX.CmdLine (defConfig)
import           GHC.Hs (cid_binds)
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.Runners.AntXML

import qualified GHC as GHC
import qualified GHC.Builtin.Names as GHC
import qualified GHC.Builtin.Types as GHC
import qualified GHC.Core as GHC
import qualified GHC.Core.Lint as GHC
import qualified GHC.Core.Type as GHC
import qualified GHC.Core.Utils as Core
import qualified GHC.Data.EnumSet as EnumSet
import qualified GHC.Data.FastString as GHC
import qualified GHC.Data.StringBuffer as GHC
import qualified GHC.Driver.Main as GHC (hscDesugar)
import qualified GHC.Driver.Config.Core.Lint as GHC
import qualified GHC.Parser as Parser
import qualified GHC.Parser.Lexer as GHC
import qualified GHC.Types.Id as GHC
import qualified GHC.Types.Name as GHC
import qualified GHC.Types.SrcLoc as GHC
import qualified GHC.Types.Unique as GHC
import qualified GHC.Unit.Module.ModGuts as GHC
import qualified GHC.Unit.Types as GHC
import qualified GHC.Utils.Error as GHC

import GHC.Paths (libdir)
import qualified WiredInTests

main :: IO ()
main =
    defaultMainWithIngredients (antXMLRunner : defaultIngredients) testTree

testTree :: TestTree
testTree =
    testGroup
        "GHC API"
        [ testCase "apiComments" testApiComments
        , testCase "caseDesugaring" testCaseDesugaring
        , testCase "numericLiteralDesugaring" testNumLitDesugaring
        , testCase "dollarDesugaring" testDollarDesugaring
        , testCase "deadBindingPreservation" testDeadBindingPreservation
        , testCase "exportedBindingNotInlined" testExportedBindingNotInlined
        , testCase "derivingCheck" testDerivingCheck
        , testCase "singleCaseCaptureAvoidance" testSingleCaseCaptureAvoidance
        , testCase "stringLiteralSortCorrespondence" testStringLiteralSortCorrespondence
        , testCase "stringLiteralDomainsRemainDistinct" testStringLiteralDomainsRemainDistinct
        , WiredInTests.tests
        ]

-- Core lambdas retain GHC type literals, whereas refinement types pass through
-- ofType. Both paths must produce the same logical sort, including embeddings.
testStringLiteralSortCorrespondence :: IO ()
testStringLiteralSortCorrespondence = do
    binds <- compileToCore "LiteralSorts" $ unlines
      [ "{-# LANGUAGE DataKinds, KindSignatures #-}"
      , "module LiteralSorts where"
      , "import GHC.TypeLits (Symbol)"
      , "newtype Tagged (label :: Symbol) = Tagged Int"
      , "nested :: Maybe (Tagged \"component id\") -> Maybe (Tagged \"component id\")"
      , "nested x = x"
      ]
    case findExpr "nested" binds of
      Nothing -> assertFailure "missing nested literal control"
      Just nested -> do
        let literal = GHC.mkStrLitTy (GHC.fsLit "component id")
            hole = GHC.mkStrLitTy (GHC.fsLit "$LH_RHOLE")
            custom = F.tceFromList
              [ (GHC.listTyCon, (F.FObj (F.symbol "CustomList"), F.NoArgs))
              , (GHC.charTyCon, (F.FObj (F.symbol "CustomChar"), F.NoArgs))
              ]
            collapsed = F.tceFromList
              [(GHC.listTyCon, (F.FObj (F.symbol "EmbeddedString"), F.WithArgs))]
            types = [literal, Core.exprType nested]
            agrees embeddings ty =
              RefType.typeSort embeddings ty @?=
                RefType.rTypeSort embeddings (RefType.ofType ty :: SpecType)
        forM_ [mempty, custom, collapsed] $ \embeddings -> do
          forM_ types (agrees embeddings)
          RefType.typeSort embeddings (GHC.mkNumLitTy 7) @?= F.FInt
          agrees embeddings hole
          assertBool "hole sentinel became a string sort"
            (RefType.typeSort embeddings hole /= RefType.typeSort embeddings literal)

-- Logical sort normalization does not change GHC's type-level label equality.
-- This is a type-equality control, not a claim about visible newtype coercions.
testStringLiteralDomainsRemainDistinct :: IO ()
testStringLiteralDomainsRemainDistinct = do
    -- First check the same template and environment with equal labels, so an
    -- unrelated source error cannot make the distinct-label control pass.
    _ <- GHC.runGhc (Just libdir) $
      typecheckSourceCode "DistinctLabels" (source "component id")
    rejected <- GHC.runGhc (Just libdir) $
      GHC.handleSourceError (\_ -> return True) $ do
        _ <- typecheckSourceCode "DistinctLabels" (source "platform name")
        return False
    assertBool "GHC identified distinct type-level labels" rejected
  where
    source label = unlines
      [ "{-# LANGUAGE DataKinds, KindSignatures #-}"
      , "module DistinctLabels where"
      , "import GHC.TypeLits (Symbol)"
      , "newtype Tagged (label :: Symbol) = Tagged Int"
      , "identity :: Tagged \"component id\" -> Tagged " ++ show label
      , "identity x = x"
      ]

-- A spelling-only test would be alpha-renamed by GHC before reaching Rewrite.
-- Instead deliberately reuse the Unique of a variable free in the outer
-- continuation as the inner case binder. Extending its scope must freshen it.
testSingleCaseCaptureAvoidance :: IO ()
testSingleCaseCaptureAvoidance = GHC.runGhc (Just libdir) $ do
    flags <- GHC.getSessionDynFlags
    let variable n = GHC.mkSysLocal (GHC.fsLit "sameName") (GHC.mkUnique 'q' n)
                      GHC.manyDataConTy GHC.intTy
        x = variable 1
        y = variable 2
        z = variable 3
        holder = variable 4
        original = Case (Case (Var y) x GHC.intTy [Alt DEFAULT [] (Var x)])
                        z GHC.intTy [Alt DEFAULT [] (Var x)]
    case rewriteBinds defConfig [GHC.NonRec holder original] of
      [GHC.NonRec _ result@(Case (Var source) fresh _
        [Alt DEFAULT [] (Case (Var innerResult) outer _ [Alt DEFAULT [] (Var answer)])])] -> do
          liftIO $ assertBool "commuting captured the outer variable"
            (source == y && fresh /= x && innerResult == fresh && outer == z && answer == x)
          case GHC.lintExpr (GHC.initLintConfig flags []) (Lam x (Lam y result)) of
            Nothing -> return ()
            Just problems -> liftIO $ assertFailure (showPprQualified problems)
      _ -> liftIO $ assertFailure "commuting did not preserve both case evaluations"

-- Tests that Liquid.GHC.API.Extra.apiComments can retrieve the comments in
-- the right order from an AST
testApiComments :: IO ()
testApiComments = do
    let str = unlines
          [ "{-@ LIQUID \"--ple\" @-}"
          , "module A where"
          , "import B"
          , ""
          , "{-@ i :: { v:Int | v>=0 } @-}"
          , "i :: Int"
          , "i = 4"
          , ""
          , "{-@ infixr ++ @-}"
          , ""
          , "{-@ abs :: Int -> { v:Int | v >= 0 } @-}"
          , "abs :: Int -> Int"
          , "abs x = z"
          , "  where"
          , "    {-@ { v: Int | z >= 0 } @-}"
          , "    z = if x < 0 then -x else x"
          ]
    lhsMod <- parseMod str "A.hs"
    let comments = map GHC.unLoc (apiCommentsParsedSource lhsMod)
        expected = map ApiBlockComment
          [ "{-@ LIQUID \"--ple\" @-}"
          , "{-@ i :: { v:Int | v>=0 } @-}"
          , "{-@ infixr ++ @-}"
          , "{-@ abs :: Int -> { v:Int | v >= 0 } @-}"
          , "{-@ { v: Int | z >= 0 } @-}"
          ]
    when (expected /= comments) $
      fail $ unlines $ "Unexpected comments:" : map show comments
  where
    parseMod str filepath = do
      let location = GHC.mkRealSrcLoc (GHC.mkFastString filepath) 1 1
          buffer = GHC.stringToStringBuffer str
          popts = GHC.mkParserOpts EnumSet.empty GHC.emptyDiagOpts False True True True
          parseState = GHC.initParserState popts buffer location
      case GHC.unP Parser.parseModule parseState of
        GHC.POk _ result -> return result
        _ -> fail "Unexpected parser error"

-- | Tests that case expressions desugar as Liquid Haskell expects.
testCaseDesugaring :: IO ()
testCaseDesugaring = do
    let inputSource = unlines
          [ "module CaseDesugaring where"
          , "f :: Bool -> ()"
          , "f x = case x of"
          , "        True -> ()"
          ]

        -- Expected desugaring:
        --
        -- CaseDesugaring.f
        --      = \ (x :: GHC.Types.Bool) ->
        --          case x of {
        --            __DEFAULT ->
        --              case Control.Exception.Base.patError ...
        --              of {
        --              };
        --            GHC.Types.True -> GHC.Tuple.()
        --          }
        --
        isExpectedDesugaring p = case findExpr "f" p of
          Just e0
            | Lam x (untick -> Case (Var x') _ _ [alt0, _alt1]) <- e0
            , x == x'
            , Alt DEFAULT [] e1 <- alt0
            , Case e2 _ _ [] <- e1
            , (Var e3,_) <- GHC.collectArgs e2
            -> e3 == pAT_ERROR_ID
          _ -> False

    coreProgram <- compileToCore "CaseDesugaring" inputSource
    unless (isExpectedDesugaring coreProgram) $
      fail $ unlines $
        "Unexpected desugaring:" : map showPprQualified coreProgram

-- | Tests that numeric literal expressions desugar as Liquid Haskell expects.
--
-- https://github.com/ucsd-progsys/liquidhaskell/issues/2237
testNumLitDesugaring :: IO ()
testNumLitDesugaring = do
    let inputSource = unlines
          [ "module NumLitDesugaring where"
          , "f :: Num a => a"
          , "f = 1"
          ]

        -- Expected desugaring:
        --
        -- NumLitDesugaring.f
        --      = \@a dict -> fromInteger @a dict (GHC.Num.Integer.IS 1#)
        --
        isExpectedDesugaring p = case findExpr "f" p of
          Just e0
            | Lam _a (Lam _dict (untick . dropLets -> App fromIntegerApp (App (Var vIS) lit))) <- e0
            , App (App (Var vFromInteger) _aty) _numDict <- fromIntegerApp
            , GHC.idName vFromInteger  == GHC.fromIntegerName
            , GHC.nameStableString (GHC.idName vIS) == GHC.nameStableString GHC.integerISDataConName
            , Lit (LitNumber LitNumInt 1) <- lit
            -> True
          _ -> False

    coreProgram <- compileToCore "NumLitDesugaring" inputSource
    unless (isExpectedDesugaring coreProgram) $
      fail $ unlines $
        "Unexpected desugaring:" : map showPprQualified coreProgram

dropLets :: GHC.CoreExpr -> GHC.CoreExpr
dropLets (Let _ e) = dropLets e
dropLets e         = e

-- | Tests that dollar sign desugars as Liquid Haskell expects.
testDollarDesugaring :: IO ()
testDollarDesugaring = do
    let inputSource = unlines
          [ "module DollarDesugaring where"
          , "f :: ()"
          , "f = (\\_ -> ()) $ 'a'"
          ]

        isExpectedDesugaring p = case findExpr "f" p of
          Just e0
            | Just (Lam _ _, App _ (Lit (LitChar 'a'))) <- splitDollarApp e0
            -> True
          _ -> False

    coreProgram <- compileToCore "DollarDesugaring" inputSource
    unless (isExpectedDesugaring coreProgram) $
      fail $ unlines $
        "Unexpected desugaring:" : map showPprQualified coreProgram

-- | Find the Core expression bound to the given name.
findExpr :: String -> GHC.CoreProgram -> Maybe GHC.CoreExpr
findExpr _ [] =
  Nothing
findExpr name (p:ps) = case p of
  GHC.NonRec b e
    | occNameString (GHC.occName b) == name
    -> Just e
  GHC.Rec binds
    | Just (_, e) <- find (\(b, _e) -> occNameString (GHC.occName b) == name) binds
    -> Just e
  _ -> findExpr name ps


compileToCore :: String -> String -> IO [GHC.CoreBind]
compileToCore modName inputSource = do
    GHC.runGhc (Just libdir) $ do
      (_, tcMod) <- typecheckSourceCode modName inputSource
      dsMod <- GHC.desugarModule tcMod
      return $ GHC.mg_binds $ GHC.dm_core_module dsMod

typecheckSourceCode
  :: GHC.GhcMonad m => String -> String -> m (GHC.ModSummary, GHC.TypecheckedModule)
typecheckSourceCode modName inputSource = do
    now <- liftIO getCurrentTime
    df1 <- GHC.getSessionDynFlags
    GHC.setSessionDynFlags $ df1 { GHC.backend = GHC.interpreterBackend }
    let target = GHC.Target
               { GHC.targetId           = GHC.TargetFile (modName ++ ".hs") Nothing
               , GHC.targetUnitId       = GHC.homeUnitId_ df1
               , GHC.targetAllowObjCode = False
               , GHC.targetContents     = Just (GHC.stringToStringBuffer inputSource, now)
               }
    GHC.setTargets [target]
    void $ GHC.depanal [] False

    ms <- GHC.getModSummary
            (GHC.mkModule GHC.mainUnit (GHC.mkModuleName modName))
    tm <- GHC.parseModule ms >>= GHC.typecheckModule
    return (ms, tm)

-- | Like 'compileToCore' but applies 'addNoInlinePragmasToBinds' before
-- desugaring, simulating what LH's plugin does to preserve bindings that
-- would otherwise be inlined away.
compileToCoreWithLH :: String -> String -> IO [GHC.CoreBind]
compileToCoreWithLH modName inputSource = do
    GHC.runGhc (Just libdir) $ do
      (ms, tcMod) <- typecheckSourceCode modName inputSource
      let (tcg, _) = GHC.tm_internals_ tcMod
          tcg' = addNoInlinePragmasToBinds tcg
      hsc_env <- GHC.getSession
      guts <- liftIO $ GHC.hscDesugar hsc_env ms tcg'
      return $ GHC.mg_binds guts

-- | Tests that dead bindings (unused where-clause bindings) are preserved
-- when 'addNoInlinePragmasToBinds' marks Ids as exported.
testDeadBindingPreservation :: IO ()
testDeadBindingPreservation = do
    let inputSource = unlines
          [ "module DeadBindingPreservation where"
          , "f :: Int -> ()"
          , "f x = ()"
          , "  where"
          , "    z = x + 1"
          ]

        -- The dead binding 'z' should still appear in the Core output.
        hasDeadBinding p = case findExpr "f" p of
          Just e -> hasLetNamed "z" e
          _      -> False

    coreProgram <- compileToCoreWithLH "DeadBindingPreservation" inputSource
    unless (hasDeadBinding coreProgram) $
      fail $ unlines $
        "Dead binding 'z' was eliminated:" : map showPprQualified coreProgram

-- | Tests that a binding marked as exported is not inlined even when it
-- occurs exactly once (i.e. it would normally be inlined by the simple
-- optimizer).
testExportedBindingNotInlined :: IO ()
testExportedBindingNotInlined = do
    let inputSource = unlines
          [ "module ExportedBindingNotInlined where"
          , "f :: Int -> Int"
          , "f x = z"
          , "  where"
          , "    z = x + 1"
          ]

        -- The binding 'z' is used exactly once. Without the exported
        -- marking, the simple optimizer would inline it. With it,
        -- 'z' should still appear as a let-binding.
        hasBinding p = case findExpr "f" p of
          Just e -> hasLetNamed "z" e
          _      -> False

    coreProgram <- compileToCoreWithLH "ExportedBindingNotInlined" inputSource
    unless (hasBinding coreProgram) $
      fail $ unlines $
        "Binding 'z' was inlined:" : map showPprQualified coreProgram

-- | Check if an expression contains a let-binding with the given name.
hasLetNamed :: String -> GHC.CoreExpr -> Bool
hasLetNamed name = go
  where
    go (Let (GHC.NonRec b _) body) =
      occNameString (GHC.occName b) == name || go body
    go (Let (GHC.Rec pairs) body) =
      any (\(b, _) -> occNameString (GHC.occName b) == name) pairs || go body
    go (Lam _ e) = go e
    go (App e1 e2) = go e1 || go e2
    go (GHC.Case _ _ _ alts) = any (\(Alt _ _ rhs) -> go rhs) alts
    go (GHC.Cast e _) = go e
    go (GHC.Tick _ e) = go e
    go _ = False

-- | Tests that the SrcSpans of methods in a class instance contain the
-- SrcSpans of the corresponding core bindings, and that the instance
-- declaration SrcSpan contains the method SrcSpans.
--
-- The instance has two methods: 'method1' (two equations) and 'method2'
-- (one equation), so the test exercises multi-equation method spans too.
testDerivingCheck :: IO ()
testDerivingCheck = do
    let inputSource = unlines
          [ "module InstMethods where"
          , "class MyClass a where"
          , "  method1 :: a -> a -> a"
          , "  method2 :: a -> Bool"
          , ""
          , "instance MyClass Int where"
          , "  method1 0 y = y"
          , "  method1 x y = x + y"
          , "  method2 x = x > 0"
          ]

    (instSpan, methodBindings, coreProgram) <-
      GHC.runGhc (Just libdir) $ do
        (_, tcMod) <- typecheckSourceCode "InstMethods" inputSource
        let (tcg, _) = GHC.tm_internals_ tcMod
        (iSpan, mBinds) <- liftIO $ case tcg_rn_decls tcg of
          Nothing  -> fail "No renamed declarations found"
          Just grp ->
            case [ ( GHC.getLocA d
                   , cid_binds inst
                   )
                 | d <- hsGroupInstDecls grp
                 , ClsInstD _ inst <- [GHC.unLoc d]
                 ] of
              [(is, bs)] -> return (is, bs)
              other      ->
                fail $ "Expected exactly one instance, got " ++ show (length other)
        dsMod <- GHC.desugarModule tcMod
        let core = GHC.mg_binds $ GHC.dm_core_module dsMod
        return (iSpan, mBinds, core)

    -- Check that the instance declaration span contains all method spans.
    forM_ methodBindings $ \mb -> do
      let ms = GHC.getLocA mb
      unless (ms `GHC.isSubspanOf` instSpan) $
        fail $ "Method span " ++ show ms ++
               " is not a subspan of instance span " ++ show instSpan

    -- Build a mapping from method names to their spans.
    let methodNameToSpans :: [(String, GHC.SrcSpan)]
        methodNameToSpans =
          [ (occNameString (GHC.occName mn), GHC.getLocA mb)
          | mb <- methodBindings
          , let bindLoc = GHC.unLoc mb
                mn = case bindLoc of
                  GHC.FunBind {GHC.fun_id = fid} -> GHC.unLoc fid
                  _ -> error "Unexpected bind type in instance"
          ]

    -- Check that each instance method core binder's span is contained in
    -- the corresponding method span. Instance method core binders have
    -- names starting with "$c" (e.g. "$cmethod1").
    let coreBinders       = concatMap collectBinders coreProgram
        instMethodBinders =
          filter (isPrefixOf "$c" . occNameString . GHC.occName) coreBinders
    when (null instMethodBinders) $
      fail "No instance method core binders found (expected names starting with $c)"
    forM_ instMethodBinders $ \v -> do
      let coreSpan = GHC.getSrcSpan v
          coreBinderName = occNameString (GHC.occName v)
          methodName = drop 2 coreBinderName  -- Remove "$c" prefix
      case lookup methodName methodNameToSpans of
        Nothing ->
          fail $ "Core binder " ++ coreBinderName ++ " does not correspond to any method"
        Just methodSpan ->
          unless (coreSpan `GHC.isSubspanOf` methodSpan) $
            fail $ "Core binder " ++ coreBinderName ++
                   " with span " ++ show coreSpan ++
                   " is not a subspan of method span " ++ show methodSpan
  where
    collectBinders :: GHC.CoreBind -> [GHC.Id]
    collectBinders (GHC.NonRec b _) = [b]
    collectBinders (GHC.Rec pairs)  = map fst pairs
