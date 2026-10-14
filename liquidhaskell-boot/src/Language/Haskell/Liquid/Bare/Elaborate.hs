{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE ExplicitForAll            #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE TemplateHaskellQuotes     #-}
{-# LANGUAGE FlexibleContexts          #-}

{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module uses GHC API to elaborate the resolves expressions

-- TODO: Genearlize to BareType and replace the existing resolution mechanisms

module Language.Haskell.Liquid.Bare.Elaborate
  ( elaborateSpecTypeWithPrimitives
  , kindCheckLogicalMeasure
  , alignQueryTelescope
  , renameCheckedPredicateOwner
  , interpretCheckedPredicate
  , freshenQueryTelescope
  -- , buildSimplifier
  )
where

import qualified Language.Fixpoint.Types       as F
import qualified Language.Fixpoint.Types.Visitor as F
import qualified Language.Fixpoint.SortCheck   as SC
import qualified Language.Fixpoint.Types.Config as FC
import           Language.Haskell.Liquid.WiredIn (wiredSortedSyms)
-- import           Control.Arrow
import           Liquid.GHC.API hiding (panic, varName)
import qualified Language.Haskell.Liquid.GHC.Misc
                                               as GM
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.RefType
                                                ( ofType, strengthen, strengthenWith, subsTyVarMeet', subts, typeSort, uTop, updateRTVar, specTypeToQueryType )
import qualified Language.Haskell.Liquid.Types.Types as T
import qualified Language.Haskell.Liquid.Bare.Axiom as Axiom
import qualified Language.Haskell.Liquid.Measure as Measure
import Language.Haskell.Liquid.Types.Visitors (letVars)
import qualified Data.List                     as L
import qualified Data.HashMap.Strict           as M
import qualified Data.HashSet                  as S
import qualified Data.Text as Text
import qualified Control.Monad.State.Strict as State
import Data.Generics (Data, everythingBut, extQ, mkQ)

import GHC.Builtin.Types (charTy, integerTy, runtimeRepTy, wordTyConName)
import GHC.Builtin.Names (int8TyConName, int16TyConName, int32TyConName, int64TyConName, word8TyConName, word16TyConName, word32TyConName, word64TyConName)
import GHC.Platform (Platform, platformMinInt, platformMaxInt, platformMaxWord)
import GHC.Driver.DynFlags (targetPlatform)
import GHC.Hs (HsMatchContext (CaseAlt), HsExpr (HsLet), HsLocalBindsLR (HsValBinds), HsValBindsLR (ValBinds), mkSimpleGeneratedFunBind, mkSimpleMatch, nlConPat, nlHsCase, nlWildPat)
import qualified GHC.Hs as Hs
import qualified GHC.Tc.Gen.HsType as TcHs
import GHC.Tc.Types.Origin (ReportRedundantConstraints (NoRRC))
import GHC.Types.Name (mkExternalName)
import GHC.Types.Name.Occurrence
import GHC.Types.Name.Reader (rdrNameOcc)
import GHC.Core.Type (getTyVar_maybe, mkSpecForAllTy, mkTYPEapp, typeKind)
import GHC.Core.Predicate (isCoVarType)
import qualified GHC.Tc.Utils.TcType as TcType
import GHC.Core.TyCon (Role (Nominal), isVisibleTyConBinder, isInferredTyConBinder, mkAnonTyConBinder)
import GHC.Core.SimpleOpt (SimpleOpts (so_eta_red), defaultSimpleOpts, simpleOptExprNoInline)
import GHC.Unit.Module (getModule)
import qualified Liquid.GHC.API as Ghc
import qualified Data.Maybe                    as Mb
import qualified GHC.Tc.Utils.Env as TcEnv
import qualified GHC.Rename.Utils as RnUtils
import GHC.Tc.Utils.Monad (getSrcSpanM, tryTc)
import qualified Text.PrettyPrint.HughesPJ as PJ
import Text.Read (readMaybe)

-- TODO: make elaboration monadic so typeclass names are unified to something
-- that is generated in advance. This can greatly simplify the implementation
-- of elaboration

-- the substitution code is meant to inline dictionary functions
-- but does not seem to work
-- lookupIdSubstAll :: O.SDoc -> M.HashMap Id CoreExpr -> Id -> CoreExpr
-- lookupIdSubstAll doc env v | Just e <- M.lookup v env = e
--                            | otherwise                = Var v
--         -- Vital! See Note [Extending the Subst]
--   -- | otherwise = WARN( True, text "CoreSubst.lookupIdSubst" <+> doc <+> ppr v
--   --                           $$ ppr in_scope)

-- substExprAll :: O.SDoc -> M.HashMap Id CoreExpr -> CoreExpr -> CoreExpr
-- substExprAll doc subst orig_expr = subst_expr_all doc subst orig_expr


-- subst_expr_all :: O.SDoc -> M.HashMap Id CoreExpr -> CoreExpr -> CoreExpr
-- subst_expr_all doc subst expr = go expr
--  where
--   go (Var v) = lookupIdSubstAll (doc O.$$ O.text "subst_expr_all") subst v
--   go (Type     ty      ) = Type ty
--   go (Coercion co      ) = Coercion co
--   go (Lit      lit     ) = Lit lit
--   go (App  fun     arg ) = App (go fun) (go arg)
--   go (Tick tickish e   ) = Tick tickish (go e)
--   go (Cast e       co  ) = Cast (go e) co
--      -- Do not optimise even identity coercions
--      -- Reason: substitution applies to the LHS of RULES, and
--      --         if you "optimise" an identity coercion, you may
--      --         lose a binder. We optimise the LHS of rules at
--      --         construction time

--   go (Lam  bndr    body) = Lam bndr (subst_expr_all doc subst body)

--   go (Let  bind    body) = Let (mapBnd go bind) (subst_expr_all doc subst body)

--   go (Case scrut bndr ty alts) =
--     Case (go scrut) bndr ty (map (go_alt subst) alts)

--   go_alt subst (con, bndrs, rhs) = (con, bndrs, subst_expr_all doc subst rhs)


-- mapBnd :: (Expr b -> Expr b) -> Bind b -> Bind b
-- mapBnd f (NonRec b e) = NonRec b (f e)
-- mapBnd f (Rec bs    ) = Rec (map (second f) bs)

-- -- substLet :: CoreExpr -> CoreExpr
-- -- substLet (Lam b body) = Lam b (substLet body)
-- -- substLet (Let b body)
-- --   | NonRec x e <- b = substLet
-- --     (substExprAll O.empty (extendIdSubst emptySubst x e) body)
-- --   | otherwise = Let b (substLet body)
-- -- substLet e = e


-- buildDictSubst :: CoreProgram -> M.HashMap Id CoreExpr
-- buildDictSubst = cata f
--  where
--   f Nil = M.empty
--   f (Cons b s) | NonRec x e <- b, isDFunId x -- || isDictonaryId x
--                                              = M.insert x e s
--                | otherwise                   = s

-- buildSimplifier :: CoreProgram -> CoreExpr -> TcRn CoreExpr
-- buildSimplifier cbs e = pure e-- do
 --  df <- getDynFlags
 --  liftIO $ simplifyExpr (df `gopt_set` Opt_SuppressUnfoldings) e'
 -- where
 --  -- fvs = fmap (\x -> (x, getUnique x, isLocalId x))  (freeVars mempty e)
 --  dictSubst = buildDictSubst cbs
 --  e'        = substExprAll O.empty dictSubst e


-- build the expression we send to ghc for elaboration
-- YL: tweak this function to see if ghc accepts explicit dictionary binders
-- returning both expressions and binders since ghc adds unique id to the expressions

-- | returns (lambda binders, forall binders)
collectSpecTypeBinders :: SpecType -> ([F.Symbol], [F.Symbol])
collectSpecTypeBinders = \case
  RFun bind _ tin tout _
    | isClassType tin -> collectSpecTypeBinders tout
    | otherwise       -> let (bs, abs') = collectSpecTypeBinders tout
                          in (bind : bs, abs')
  RAllT (RTVar (RTV ab) _) t _ ->
    let (bs, abs') = collectSpecTypeBinders t
     in (bs, F.symbol ab : abs')
  RAllP _ t -> collectSpecTypeBinders t
  REx _ _ t -> collectSpecTypeBinders t
  RAppTy _ t _ -> collectSpecTypeBinders t
  RRTy _ _ _ t -> collectSpecTypeBinders t
  _ -> ([], [])

-- really should be fused with collectBinders. However, we need the binders
-- to correctly convert fixpoint expressions to ghc expressions because of
-- namespace related issues (whether the symbol denotes a varName or a datacon)
-- Query locals are fresh exact Names, not qualified source names. References
-- use the innermost owner of each logical label; the caller restores original
-- logical binders after elaboration, independently of these temporary names.
buildHsExpr :: (M.HashMap F.Symbol RdrName -> LHsExpr GhcPs) -> SpecType -> TcRn (LHsExpr GhcPs)
buildHsExpr result = go M.empty
  where
    go bound = \case
      RFun bind _ tin tout _
        | isClassType tin -> go bound tout
        | otherwise -> do
            unique <- getUniqueM
            let name = nameRdrName (mkInternalName unique (mkVarOcc "lh_query") noSrcSpan)
            body <- go (M.insert bind name bound) tout
            pure (mkHsLam (noLocA [nlVarPat name]) body)
      RAllT _ t _ -> go bound t
      RAllP _ t -> go bound t
      REx _ _ t -> go bound t
      RAppTy _ t _ -> go bound t
      RRTy _ _ _ t -> go bound t
      _ -> pure (result bound)


-- Sort annotations inhabit the type namespace, not the term telescope.
-- Keep every source binder and occurrence (including predicate defaults),
-- without evaluating the declaration capabilities stored inside a sort.
querySourceSymbols :: (Data a) => a -> S.HashSet F.Symbol
querySourceSymbols = everythingBut S.union (mkQ (S.empty, False) symbol `extQ` sort)
  where
    symbol name = (S.singleton name, True)
    sort :: F.Sort -> (S.HashSet F.Symbol, Bool)
    sort _ = (S.empty, True)

-- Give every query parameter a distinct lexical coordinate. An arrow's
-- domain sees the enclosing owners; its result sees its own owner instead.
-- Anonymous markers own no occurrences, while explicit collisions require
-- capture-avoiding substitution in precisely their lexical scope.
freshenQueryTelescope :: Bool -> [F.Symbol] -> SpecType -> SpecType
freshenQueryTelescope bindSelf reserved original = State.evalState (go M.empty original) occupied
  where
    occupied = S.fromList reserved `S.union` querySourceSymbols original
    substitute owners = F.subst (F.mkSubst [(name, meaning) | (name, meaning) <- M.toList owners, meaning /= F.EVar name])
    substituteRef owners (MkUReft (F.Reft (value, predicate)) abstract) =
        let local = M.delete value owners
         in MkUReft (F.Reft (value, substitute local predicate)) (substitute local abstract)
    bind name owner = M.insert name (F.EVar owner)
    freshOwner owners name
        | name == "" || F.isDummy name || M.member name owners =
            State.state (\names -> let (names', fresh) = F.freshInNS "lh_query_owner" names in (fresh, names'))
        | otherwise = pure name
    extend owners name name'
        | name == "" || F.isDummy name = owners
        | otherwise = bind name name' owners
    go :: M.HashMap F.Symbol F.Expr -> SpecType -> State.State (S.HashSet F.Symbol) SpecType
    go owners (RFun name info domain result reft) = do
        domain' <- go owners domain
        name' <- freshOwner owners name
        let resultOwners = extend owners name name'
        RFun name' info domain' <$> go resultOwners result <*> pure (substituteRef owners reft)
    go owners (RAllT variable rest reft) = do
        (variable', bodyOwners) <- case ty_var_info variable of
            RTVNoInfo{} -> pure (variable, owners)
            info@RTVInfo{rtv_name = name, rtv_kind = kind} -> do
                name' <- case rTVarToBind variable of
                    Just _ -> freshOwner owners name
                    Nothing -> pure name
                let variable' = variable{ty_var_info = info{rtv_name = name', rtv_kind = substitute owners kind}}
                    bodyOwners = case rTVarToBind variable of
                        Just _ -> extend owners name name'
                        Nothing -> owners
                pure (variable', bodyOwners)
        RAllT variable' <$> go bodyOwners rest <*> pure (substituteRef owners reft)
    go owners (RAllP predicate rest) = do
        let (resultOwners, arguments) =
                L.mapAccumL
                    ( \scope (domain, name, actual) ->
                        let scope' = M.delete name scope
                         in (scope', (substitute scope domain, name, substitute scope' actual))
                    )
                    owners
                    (pargs predicate)
            predicate' = predicate{ptype = substitute resultOwners (ptype predicate), pargs = arguments}
        RAllP predicate' <$> go owners rest
    go owners (RApp constructor arguments predicates reft@(MkUReft (F.Reft (value, _)) _)) =
        let argumentOwners = if bindSelf then M.delete value owners else owners
         in RApp constructor <$> traverse (go argumentOwners) arguments <*> traverse (property owners) predicates <*> pure (substituteRef owners reft)
    go owners (RAppTy function argument reft) = RAppTy <$> go owners function <*> go owners argument <*> pure (substituteRef owners reft)
    go owners (REx name witness rest) = do
        witness' <- go owners witness
        name' <- freshOwner owners name
        REx name' witness' <$> go (extend owners name name') rest
    go owners (RRTy environment reft obligation rest) = do
        (environment', localOwners) <- context (obligation == OCons) owners environment
        let reftOwners = if obligation == OCons then owners else localOwners
        RRTy environment' (substituteRef reftOwners reft) obligation <$> go owners rest
    go owners (RVar variable reft) = pure (RVar variable (substituteRef owners reft))
    go owners (RHole reft) = pure (RHole (substituteRef owners reft))
    go owners ty = pure (substitute owners ty)
    property owners (RProp formals body) = do
        (formals', local) <- formalOwners owners formals
        RProp formals' <$> go local body
    formalOwners owners [] = pure ([], owners)
    formalOwners owners ((name, domain) : rest) = do
        name' <- freshOwner owners name
        (rest', local) <- formalOwners (extend owners name name') rest
        pure ((name', substitute owners domain) : rest', local)
    context _ owners [] = pure ([], owners)
    context True owners [(left, lhs), (right, rhs)] =
        (\lhs' rhs' -> ([(left, lhs'), (right, rhs')], owners)) <$> go owners lhs <*> go owners rhs
    context endpoints owners ((name, domain) : rest) = do
        domain' <- go owners domain
        name' <- freshOwner owners name
        (rest', localOwners) <- context endpoints (extend owners name name') rest
        pure ((name', domain') : rest', localOwners)

-- Interpret exactly the lambda telescope GHC checked. Type substitution is
-- scoped and nominal: equal logical sorts never identify different carriers.
-- Logical predicate quantifiers introduce no GHC lambda. Dictionaries are
-- paired by their checked types, independently of their printed names.
alignQueryTelescope :: SpecType -> CoreExpr -> Either String T.QueryTelescope
alignQueryTelescope = go [] [] []
  where
    go sourceTypes actualTypes terms signature (Tick _ expression) =
        go sourceTypes actualTypes terms signature expression
    -- A nonrecursive let introduces no type or source-arrow parameter. Look
    -- through its body only for telescope metadata; the caller retains the
    -- whole checked Core, including this binding, for checking and readback.
    go sourceTypes actualTypes terms signature (Let (NonRec _ _) expression) =
        go sourceTypes actualTypes terms signature expression
    go sourceTypes actualTypes terms (RAllP _ rest) expression =
        go sourceTypes actualTypes terms rest expression
    go sourceTypes actualTypes terms (RAllT (ty_var_value -> RTV source) rest _) (Lam actual expression)
        | isTyVar source && isTyVar actual
        , eqType (substTyWith sourceTypes actualTypes (tyVarKind source)) (tyVarKind actual) =
            go (sourceTypes ++ [source]) (actualTypes ++ [mkTyVarTy actual]) terms rest expression
    go _ _ terms (RFun name _ domain _ _) _
        | isClassType domain
        , any (\(owner, actual) -> isDictId actual && owner == name) terms =
            Left "Distinct query dictionaries share an explicit source owner"
    go sourceTypes actualTypes terms (RFun name _ domain rest _) (Lam actual expression)
        | let expected = substTyWith sourceTypes actualTypes (specTypeToQueryType domain)
        , isId actual
        , isCoVar actual == isCoVarType expected
        , eqType expected (varType actual) =
            go sourceTypes actualTypes (terms ++ [(name, actual)]) rest expression
    go sourceTypes actualTypes terms result expression
        | not (hasBinder result)
        , eqType (substTyWith sourceTypes actualTypes (specTypeToQueryType result)) (exprType expression) =
            Right (T.QueryTelescope (zip sourceTypes actualTypes) terms)
    go sourceTypes actualTypes _ signature expression =
        Left $ "GHC predicate elaboration changed its typed source telescope\nExpected remaining type: "
            ++ showPprQualified (substTyWith sourceTypes actualTypes (specTypeToQueryType signature))
            ++ "\nActual remaining type: " ++ showPprQualified (exprType expression)
            ++ "\nActual remaining Core: " ++ showPprQualified expression
    hasBinder RAllT{} = True
    hasBinder RAllP{} = True
    hasBinder RFun{} = True
    hasBinder _ = False

-- Re-present one checked value owner in its resident refinement namespace.
-- This is alpha-renaming, not an application to an arbitrary logical actual:
-- retain the checked formal/Core identities and their nominal type images,
-- while acting simultaneously on both views of the closure's interpretation.
renameCheckedPredicateOwner :: Type -> F.Symbol -> F.Symbol -> T.CheckedPredicate -> Either String T.CheckedPredicate
renameCheckedPredicateOwner expected source destination checked =
    case [actual | (owner, actual) <- T.queryValueOwners telescope, owner == source, isId actual, not (isCoVar actual)] of
        [actual]
            | eqType (varType actual) nominal ->
                Right
                    checked
                        { T.predicateReadback = readback
                        , T.predicateDefinitions = [(owner, F.subst action meaning) | (owner, meaning) <- T.predicateDefinitions checked]
                        , T.predicateSupport = T.retainLogicSupport (F.syms readback) (T.predicateSupport checked)
                        }
        _ -> Left "Refinement owner renaming lacks its exact checked nominal carrier"
  where
    telescope = T.predicateTelescope checked
    images = T.queryTypeOwners telescope
    nominal = substTyWith (map fst images) (map snd images) expected
    action = F.mkSubst [(source, F.EVar destination)]
    readback = F.subst action (T.predicateReadback checked)

-- Core and its denotations use the checked native type owners. Only the final
-- interpretation projects those coordinates into the authored sort namespace.
-- Derive this action from the same nominal alignment, also when reinterpreting
-- a transported closure; the stored readback is not an input to interpretation.
interpretCheckedPredicate ::
    (F.TCEmb TyCon -> [(Id, F.Expr)] -> CoreExpr -> (F.Expr, T.LogicSupport)) ->
    T.CheckedPredicate ->
    (F.Expr, T.LogicSupport)
interpretCheckedPredicate interpret checked =
    (readback, T.retainLogicSupport (F.syms readback) [(owner, F.sortSubst action sort) | (owner, sort) <- support])
  where
    (meaning, support) = interpret (T.predicateEmbeddings checked) (T.predicateDefinitions checked) (T.predicateCore checked)
    action =
        F.mkSortSubst
            [(F.symbol actual, F.FObj (F.symbol source)) | (source, actualType) <- T.queryTypeOwners (T.predicateTelescope checked), Just actual <- [getTyVar_maybe actualType]]
    readback = F.applyCoSub action meaning

-- The same typed query supplies checking obligations and logical readback.
-- Generated values have explicit denotations, while source values and their
-- dictionaries are interpreted from the Core produced by GHC.
elaborateSpecTypeWithPrimitives ::
    Bool ->
    FC.ElabFlags ->
    Maybe F.SymEnv ->
    F.TCEmb TyCon ->
    [(F.Symbol, T.MeasureKind, SpecType)] ->
    [(F.Symbol, [(DataCon, Int)])] ->
    [(F.Symbol, TyCon, SpecType)] ->
    [(F.Symbol, Id)] ->
    [Var] ->
    (T.CheckedPredicate -> TcRn ()) ->
    (F.TCEmb TyCon -> [(Id, F.Expr)] -> CoreExpr -> (F.Expr, T.LogicSupport)) ->
    SpecType ->
    TcRn T.CheckedSpecType
elaborateSpecTypeWithPrimitives bindSelf flags native embeddings measures projections instances allSources captures collect interpret ty =
    RnUtils.bindLocalNames (map getName (reverse captures)) $
        TcEnv.tcExtendTyVarEnv (filter isTyVar captures) $
            TcEnv.tcExtendIdEnv (filter isId captures) $ do
                location <- getSrcSpanM
                let declarations =
                        F.fromListSEnv $
                            wiredSortedSyms
                                ++ [(name, typeSort embeddings (logicalDeclarationType kind ty)) | (name, kind, ty) <- measures]
                                ++ [(name, typeSort embeddings (sourceRho (idType identifier))) | (name, identifier) <- sources]
                    sourceRho sourceType =
                        let (variables, _, rho) = TcType.tcSplitSigmaTy sourceType
                         in foldr mkSpecForAllTy rho variables
                    logicalDeclarationType T.MsReflect = sourceRho . specTypeToQueryType
                    logicalDeclarationType _ = specTypeToQueryType
                    query resultType signature expression = do
                        (core, checkedType, logicalEmbeddings, definitions, parameters) <- primitiveQuery flags native location embeddings measures projections instances sources declarations resultType signature expression
                        telescope <- case alignQueryTelescope checkedType core of
                            Left message -> uError (ErrTySpec location (Just "refinement formation") "refinement" (F.pprint signature) (PJ.text message))
                            Right alignment -> pure alignment
                        let owners = [(actual, F.EVar owner) | (owner, actual) <- T.queryValueOwners telescope, not (isCoVar actual)]
                            (expression', support) = interpretCheckedPredicate interpret checked
                            checked =
                                T.CheckedPredicate
                                    { T.predicateCore = core
                                    , T.predicateSignature = checkedType
                                    , T.predicateTelescope = telescope
                                    , T.predicateReadback = expression'
                                    , T.predicateDefinitions = definitions ++ owners
                                    , T.predicateEmbeddings = logicalEmbeddings <> embeddings
                                    , T.predicateSupport = support
                                    , T.predicateLogicalParameters = parameters
                                    }
                        pure checked
                let reserved = map fst wiredSortedSyms ++ [name | (name, _, _) <- measures] ++ map fst projections ++ [name | (name, _, _) <- instances] ++ map fst sources ++ map F.symbol captures ++ maybe [] (map fst . F.toListSEnv . F.seSort) native
                    named = freshenQueryTelescope bindSelf reserved ty
                elaborateSpecType' query collect id named
  where
    -- Name resolution prefers an authored logical declaration to a
    -- same-spelled source value (as upstream's resolveLogicName does), so
    -- that value is not what the refinement names. Generated measures
    -- (selectors, checkers, reflections) denote their source owner.
    authored = S.fromList [name | (name, kind, _) <- measures, kind `elem` [T.MsMeasure, T.MsAbsMeasure, T.MsClass]]
    sources = filter (not . (`S.member` authored) . fst) allSources

-- The target's machine ranges of GHC's fixed-width integral carriers.
fixedWidthRange :: Platform -> TyCon -> Maybe (Integer, Integer)
fixedWidthRange platform constructor
    | name == intTyConName = Just (platformMinInt platform, platformMaxInt platform)
    | name == wordTyConName = Just (0, platformMaxWord platform)
    | otherwise = lookup name
        [ (int8TyConName, (-2 ^ (7 :: Int), 2 ^ (7 :: Int) - 1))
        , (int16TyConName, (-2 ^ (15 :: Int), 2 ^ (15 :: Int) - 1))
        , (int32TyConName, (-2 ^ (31 :: Int), 2 ^ (31 :: Int) - 1))
        , (int64TyConName, (-2 ^ (63 :: Int), 2 ^ (63 :: Int) - 1))
        , (word8TyConName, (0, 2 ^ (8 :: Int) - 1))
        , (word16TyConName, (0, 2 ^ (16 :: Int) - 1))
        , (word32TyConName, (0, 2 ^ (32 :: Int) - 1))
        , (word64TyConName, (0, 2 ^ (64 :: Int) - 1))
        ]
  where
    name = tyConName constructor

freshenLogicalType :: SpecType -> TcRn SpecType
-- Logical declarations distinguish synthetic variables by occurrence as
-- well as Unique. GHC uses only Unique, so alpha-rename the telescope before
-- interpreting it as a GHC type. Existing substitution retains refinements.
freshenLogicalType (RAllT variable@(ty_var_value -> old@(RTV tv)) rest reft) = do
    unique <- getUniqueM
    let new = RTV (setVarUnique tv unique)
    rest' <- freshenLogicalType (subsTyVarMeet' (old, RVar new mempty) rest)
    pure (RAllT variable{ty_var_value = new} rest' (subts [(old, RVar new mempty :: RSort)] reft))
freshenLogicalType ty = pure ty

-- Logical declarations have no source Id whose type can supply inferred kinds.
-- Ask GHC once for the whole declaration, before deriving checking or export
-- views. Imported declarations have complete type arguments, not source syntax.
kindCheckLogicalMeasure :: Bool -> T.Measure SpecType ctor -> TcRn (T.Measure SpecType ctor)
kindCheckLogicalMeasure complete declaration
    | T.msKind declaration `elem` [T.MsSelector, T.MsChecker, T.MsLifted, T.MsReflect] = pure declaration
    | otherwise = do
        (checked, substitution) <- kindCheckLogicalType complete (T.msSort declaration)
        let renamed = T.mapMeasureTy (\ty -> foldl (flip subsTyVarMeet') ty substitution) declaration
            sorts = M.fromList [(F.symbol old, typeSort mempty (specTypeToQueryType replacement)) | (old, replacement) <- substitution]
            expression = F.applyCoSub sorts
            body (T.E e) = T.E (expression e)
            body (T.P e) = T.P (expression e)
            body (T.R x e) = T.R x (expression e)
        pure
            renamed
                { T.msSort = checked
                , T.msEqns = [equation{T.body = body (T.body equation)} | equation <- T.msEqns renamed]
                , T.msUnSorted = [(scope, expression e) | (scope, e) <- T.msUnSorted renamed]
                }

kindCheckLogicalType :: Bool -> SpecType -> TcRn (SpecType, [(RTyVar, SpecType)])
kindCheckLogicalType complete original = do
    location <- getSrcSpanM
    ty <- freshenLogicalType original
    inferred <-
        TcHs.tcHsSigType (TcHs.ExprSigCtxt NoRRC) $
            noLocA (Hs.HsSig noExtField (Hs.HsOuterImplicit []) (syntaxType ty))
    let inferredBinders = map fst (ty_vars (toRTypeRep (ofType inferred :: SpecType)))
        variables = map (toTyVar . ty_var_value) inferredBinders
        representation = toRTypeRep ty
        declared = ty_vars representation
        matching (variable, _) =
            case [v | v <- variables, getName v == getName (toTyVar (ty_var_value variable))] of
                [v] -> (ty_var_value variable, RTV v)
                _ -> panic Nothing "Logical kind checking changed a declared type-variable owner"
        substitution = map matching declared
        authoredBody =
            foldl
                (\t (old, new) -> subsTyVarMeet' (old, RVar new mempty) t)
                (fromRTypeRep representation{ty_vars = []})
                substitution
        inferredBody = fromRTypeRep (toRTypeRep (ofType inferred :: SpecType)){ty_vars = []}
        body = Mb.fromMaybe authoredBody (alignArguments inferredBody authoredBody)
        root variable =
            Mb.fromMaybe mempty $
                lookup
                    (getName variable)
                    [ (getName (toTyVar (ty_var_value v)), subts [(old, RVar new mempty :: RSort) | (old, new) <- substitution] reft)
                    | (v, reft) <- declared
                    ]
        binder variable = case [v | (v, _) <- declared, getName (toTyVar (ty_var_value v)) == getName (toTyVar (ty_var_value variable))] of
            [v] ->
                let updated =
                        updateRTVar
                            ((subts [(old, RVar new mempty :: RSort) | (old, new) <- substitution] v){ty_var_value = ty_var_value variable})
                 in updated{ty_var_info = (ty_var_info updated){rtv_is_pol = rtv_is_pol (ty_var_info v)}}
            _ -> variable
        result = foldr (\variable rest -> RAllT (binder variable) rest (root (toTyVar (ty_var_value variable)))) body inferredBinders
        transport =
            [ (ty_var_value old, RVar new mempty)
            | ((old, _), (fresh, _)) <- zip (ty_vars (toRTypeRep original)) declared
            , Just new <- [lookup (ty_var_value fresh) substitution]
            ]
    if toRSort result == toRSort (ofType inferred :: SpecType) && eqType (specTypeToQueryType result) inferred
        then pure (result, transport)
        else
            uError
                ( ErrTySpec
                    location
                    (Just "logical declaration")
                    "refinement"
                    (F.pprint original)
                    (PJ.text "logical declaration requires implicit type arguments or nested kinds not present in its refinement type")
                )
  where
    toTyVar (RTV variable) = variable
    -- Authored applications contain visible arguments. Insert only the kind
    -- arguments GHC inferred at invisible binders, retaining every authored
    -- refinement and checking the completed type against GHC below.
    alignArguments (RFun _ _ domain result _) (RFun x info domain' result' reft) =
        RFun x info <$> alignArguments domain domain' <*> alignArguments result result' <*> pure reft
    alignArguments (RApp c arguments _ _) (RApp c' arguments' predicates reft)
        | c == c'
        , complete =
            if length arguments == length arguments'
                then (\xs -> RApp c' xs predicates reft) <$> sequence (zipWith alignArguments arguments arguments')
                else Nothing
        | c == c' = (\xs -> RApp c' xs predicates reft) <$> align (tyConBinders (rtc_tc c)) arguments arguments'
      where
        align _ [] [] = Just []
        align (binder : binders) (t : ts) us
            | not (isVisibleTyConBinder binder) = (t :) <$> align binders ts us
        align (_ : binders) (t : ts) (u : us) = (:) <$> alignArguments t u <*> align binders ts us
        align [] (t : ts) (u : us) = (:) <$> alignArguments t u <*> align [] ts us
        align _ _ _ = Nothing
    alignArguments (RAppTy function argument _) (RAppTy function' argument' reft) =
        RAppTy <$> alignArguments function function' <*> alignArguments argument argument' <*> pure reft
    alignArguments inferred (RAllP predicate authored) = RAllP predicate <$> alignArguments inferred authored
    alignArguments inferred authored
        | toRSort inferred == toRSort authored = Just authored
        | otherwise = Nothing
    syntaxType :: RType RTyCon RTyVar r -> LHsType GhcRn
    syntaxType (RVar (RTV variable) _) = Hs.nlHsTyVar NotPromoted (getName variable)
    syntaxType (RAllT variable rest _) =
        noLocA $
            Hs.HsForAllTy
                noExtField
                ( Hs.mkHsForAllInvisTele
                    noAnn
                    [ noLocA
                        (Hs.HsTvb noAnn Ghc.SpecifiedSpec (Hs.HsBndrVar noExtField (noLocA (getName (toTyVar (ty_var_value variable))))) kind)
                    ]
                )
                (syntaxType rest)
      where
        kind = case ty_var_info variable of
            RTVNoInfo{} -> Hs.HsBndrNoKind noExtField
            RTVInfo{rtv_kind = k} -> Hs.HsBndrKind noExtField (syntaxType k)
    syntaxType (RFun _ _ domain rest _)
        | isClassType domain = noLocA (Hs.HsQualTy noExtField (noLocA [syntaxType domain]) (syntaxType rest))
        | otherwise = Hs.nlHsFunTy (syntaxType domain) (syntaxType rest)
    syntaxType (RApp RTyCon{rtc_tc = tc} arguments _ _) =
        foldl apply (Hs.nlHsTyVar NotPromoted (getName tc)) $
            zip (map Just (tyConBinders tc) ++ repeat Nothing) (filter notExprArg arguments)
      where
        apply function (Just binder, _) | complete && isInferredTyConBinder binder = function
        apply function (Just binder, argument)
            | complete && not (isVisibleTyConBinder binder) = noLocA (Hs.HsAppKindTy noExtField function (syntaxType argument))
        apply function (_, argument)
            | otherwise = Hs.nlHsAppTy function (syntaxType argument)
    syntaxType (RAppTy function argument _) = Hs.nlHsAppTy (syntaxType function) (syntaxType argument)
    syntaxType (RLit literal) = noLocA $ Hs.HsTyLit noExtField $ case literal of
        NumTyLit n -> Hs.HsNumTy NoSourceText n
        StrTyLit s -> Hs.HsStrTy NoSourceText s
        CharTyLit c -> Hs.HsCharTy NoSourceText c
    syntaxType (RAllP _ rest) = syntaxType rest
    syntaxType (REx _ _ rest) = syntaxType rest
    syntaxType (RRTy _ _ _ rest) = syntaxType rest
    syntaxType _ = panic Nothing "Unresolved logical declaration in kind checking"

-- These parameters interpret the logical language, not source class methods.
-- Their result contracts preserve each original operator. They are local to
-- the generated query and are never published as source assumptions.
-- The body result belongs to the query's hole, not to a flattened telescope:
-- local foralls may occur after arrows, and a future hole may itself be a
-- function. Keep its checked nominal carrier until logical interpretation.
primitiveQuery ::
    FC.ElabFlags ->
    Maybe F.SymEnv ->
    SrcSpan ->
    F.TCEmb TyCon ->
    [(F.Symbol, T.MeasureKind, SpecType)] ->
    [(F.Symbol, [(DataCon, Int)])] ->
    [(F.Symbol, TyCon, SpecType)] ->
    [(F.Symbol, Id)] ->
    F.SEnv F.Sort ->
    Type ->
    SpecType ->
    F.Expr ->
    TcRn (CoreExpr, SpecType, F.TCEmb TyCon, [(Id, F.Expr)], [Id])
primitiveQuery flags native location embeddings measures projections instances sources declarations resultType signature original = do
    (expression, (parameters, logicalEmbeddings, projectors)) <- State.runStateT (lower contextual) ([], mempty, [])
    (core, checkedType) <- elaborate parameters projectors expression
    -- GHC checks the complete telescope. Its exposed lambda prefix is still
    -- needed to attach meanings to the actual Core binders.
    let actualParameters = take (length parameters) [identifier | identifier <- fst (collectBinders core), isId identifier]
        parameterDefinitions = zip actualParameters [meaning | (_, _, meaning) <- parameters]
        projectorDefinitions =
            [ case [identifier | identifier <- letVars core, getName identifier == owner] of
                [identifier] -> (identifier, meaning)
                _ -> die "generated source projector lost its exact Core owner"
            | (owner, _, _, meaning) <- projectors
            ]
    if length actualParameters /= length parameters
        then die "generated primitive query lost its parameter prefix"
        else pure (core, checkedType, logicalEmbeddings, parameterDefinitions ++ projectorDefinitions, actualParameters)
  where
    elaborate parameters projectors expression = do
        -- Source type variables scope over all primitive parameters as well.
        let checkedType = prependParameters signature
            prependParameters (RAllT variable rest reft) = RAllT variable (prependParameters rest) reft
            prependParameters (RAllP predicate rest) = RAllP predicate (prependParameters rest)
            prependParameters rest = foldr (\(name, ty, _) -> rFun name ty) rest parameters
        body <- buildHsExpr (\locals -> foldr bindProjector (expression locals) projectors) checkedType
        let expected = specTypeToQueryType checkedType
        elaborated <- GM.elabRnExprWithType body expected
        -- Checking polymorphic arguments can introduce beta wrappers between
        -- source lambdas. Discharge these with GHC's capture-safe simplifier,
        -- without eta reduction or unfolding source definitions. All query
        -- consumers use this one checked Core and its exact binder identities.
        let core = simpleOptExprNoInline defaultSimpleOpts{so_eta_red = False} elaborated
        if exprType elaborated `eqType` expected && exprType core `eqType` expected
            then pure (core, checkedType)
            else reject (PJ.text "Administrative query normalization changed its checked source type")
    bound = S.fromList (fst (collectSpecTypeBinders signature))
    sourceIds = M.fromList sources
    measureTypes = M.fromList [(name, (kind, ty)) | (name, kind, ty) <- measures]
    projectionCases = M.fromList projections
    -- Infer logical instantiations in the complete predicate, not separately
    -- at each application. Result-only variables (for example Set_empty's
    -- element) get their meaning from the surrounding equality. These casts
    -- annotate only the checking query; the authored refinement is unchanged.
    contextual =
        either (reject . PJ.vcat . map F.errMsg . F.errs) id $
            SC.annotateExprEAt
                flags
                native
                environment
                "refinement formation"
                (Just (typeSort embeddings resultType))
                original
      where
        -- These rows declare term values, including lexical captures. None
        -- declares a sort alias: a term label cannot give an FObj its meaning.
        environment =
            F.fromListSEnv [(name, typeSort embeddings (specTypeToQueryType ty)) | (name, ty) <- telescope signature]
                <> declarations
        telescope (RAllT _ rest _) = telescope rest
        telescope (RAllP _ rest) = telescope rest
        telescope (RFun binder _ domain rest _) = (binder, domain) : telescope rest
        telescope (REx _ _ rest) = telescope rest
        telescope (RRTy _ _ _ rest) = telescope rest
        telescope _ = []
    occupied = map (rdrNameOcc . varSymbolToRdrName) (M.keys sourceIds ++ S.toList (bound `S.union` F.syms original))
    bool = ofType boolTy :: SpecType
    integer = ofType integerTy :: SpecType
    x = "lh_primitive_x"
    value = "lh_primitive_result"
    equality result expression =
        strengthen result $
            uTop $
                F.Reft
                    (value, F.PAtom F.Eq (F.EVar value) expression)
    proposition expression =
        strengthen bool $
            uTop $
                F.Reft
                    (value, F.PIff (F.EVar value) expression)
    apply name arguments = foldl F.EApp (F.EVar name) arguments
    isSource name = name `S.member` bound || M.member name sourceIds
    -- Sort rejection is a source specification error, not a compiler panic.
    -- Reuse the ordinary Bare diagnostic, preserving its located query owner.
    reject :: PJ.Doc -> a
    reject message = uError (ErrTySpec location (Just "refinement formation") "refinement" (F.pprint signature) message)
    die :: String -> a
    die message = panic (Just location) ("Refinement primitive lowering: " ++ message)

    freshName = do
        unique <- State.lift getUniqueM
        let name = F.symbol ("lh_formation_" ++ show (getKey unique))
        if rdrNameOcc (varSymbolToRdrName name) `elem` occupied
            then freshName
            else pure name
    freshParameter ty meaning = do
        name <- freshName
        State.modify' (\(parameters, logicalEmbeddings, projectors) -> (parameters ++ [(name, ty, meaning)], logicalEmbeddings, projectors))
        pure (variable name)
    functionMeaning arguments body = do
        environment <- queryEmbeddings
        pure (foldr F.ELam body [(binder, typeSort environment ty) | (binder, ty) <- arguments])
    polymorphicType kind make = do
        unique <- State.lift getUniqueM
        let variable = mkTyVar (mkInternalName unique (mkTyVarOcc "lh_primitive_type") noSrcSpan) kind
            ty = RVar (RTV variable) mempty
        pure (RAllT (makeRTVar (RTV variable)) (make ty) mempty)
    scopeVariables :: SpecType -> [TyVar]
    scopeVariables (RAllT (ty_var_value -> RTV variable) rest _) = variable : scopeVariables rest
    scopeVariables (RFun _ _ _ rest _) = scopeVariables rest
    scopeVariables (RAllP _ rest) = scopeVariables rest
    scopeVariables (REx _ _ rest) = scopeVariables rest
    scopeVariables _ = []

    queryEmbeddings = State.gets (\(_, logicalEmbeddings, _) -> logicalEmbeddings <> embeddings)

    -- Canonical primitive carriers interpret the fixed logical vocabulary:
    -- Bool as Bool, mathematical integers as Integer, and Char as GHC Char
    -- (the same charSort used by CoreToLogic.mkC). This is not an inverse
    -- lookup in user embeddings: e.g. Word32's integer meaning stays Integer.
    -- Logical aggregate values have no source data constructors or source
    -- invariants. Their fresh GHC identity prevents accidental consumption by
    -- a source function; only their explicit logical interpretation is shared.
    -- Real type arguments, rather than free variables hidden in an embedding,
    -- make this interpretation commute with forall instantiation.
    logicalType variables sort
        | sort == F.boolSort = pure bool
        | sort == F.FInt = pure integer
        | sort == F.charSort = pure (ofType charTy)
        | sort == F.FReal = aggregate F.FReal []
        | F.FObj name <- sort
        , Just variable <- lookup name [(F.symbol v, v) | v <- variables] =
            abstract variable
        | otherwise = case sortApplication sort of
            (headSort@F.FTC{}, arguments) -> aggregate headSort arguments
            (headSort@F.FObj{}, []) -> aggregate headSort []
            _ -> die ("logical result has no closed carrier interpretation: " ++ F.showpp sort)
      where
        abstract variable = do
            local <- State.gets (\(_, current, _) -> current)
            constructor <- case [ tc
                                | (tc, (F.FObj name, F.WithArgs)) <- F.tceToList local
                                , [formal] <- [tyConTyVars tc]
                                , name == F.symbol formal
                                , eqType (tyVarKind formal) (tyVarKind variable)
                                ] of
                [tc] -> pure tc
                [] -> do
                    formal <- freshTypeVariable (tyVarKind variable)
                    logicalConstructor [formal] (F.FObj (F.symbol formal), F.WithArgs)
                _ -> die "abstract logical result has multiple query-local representations"
            pure (ofType (mkTyConApp constructor [mkTyVarTy variable]))
        aggregate headSort arguments = do
            argumentTypes <- traverse (logicalType variables) arguments
            local <- State.gets (\(_, current, _) -> current)
            constructor <- case [tc | (tc, (meaning, F.NoArgs)) <- F.tceToList local, meaning == headSort, tyConArity tc == length arguments] of
                [tc] -> pure tc
                [] -> do
                    typeVariables <- traverse (const (freshTypeVariable liftedTypeKind)) arguments
                    logicalConstructor typeVariables (headSort, F.NoArgs)
                _ -> die "logical constructor has multiple query-local representations"
            pure (ofType (mkTyConApp constructor (map specTypeToQueryType argumentTypes)))
    logicalConstructor variables (meaning, arguments) = do
        unique <- State.lift getUniqueM
        owner <- State.lift getModule
        let name = mkExternalName unique owner (mkTcOcc ("LHLogicalValue_" ++ show (getKey unique))) noSrcSpan
            tc = Ghc.mkPrimTyCon name (map mkAnonTyConBinder variables) liftedTypeKind (map (const Nominal) variables)
        State.modify' (\(parameters, current, projectors) -> (parameters, F.tceInsert tc meaning arguments current, projectors))
        pure tc
    freshTypeVariable kind = do
        unique <- State.lift getUniqueM
        pure (mkTyVar (mkInternalName unique (mkTyVarOcc "lh_logical_argument") noSrcSpan) kind)
    sortApplication = go []
      where
        go arguments (F.FApp function argument) = go (argument : arguments) function
        go arguments function = (function, arguments)

    theory expected name schema =
        logicalOperation False expected [(name, schema)] (apply name)

    -- The fixpoint judgment owns both the primitive and its result sort.
    -- Source operands retain their independently elaborated GHC types; no
    -- source Num/Eq dictionary supplies logical arithmetic or relation meaning.
    logicalOperation generalize expected declarations operation arguments =
        traverse lower arguments >>= logicalOperationOn generalize expected declarations operation
    logicalOperationOn generalize expected declarations operation lowered = do
        types <-
            if generalize
                then do
                    -- Infer the homogeneous equality instance jointly: a
                    -- polymorphic operand gets context from its sibling.
                    -- This probe contributes no facts or checking Core.
                    query <- State.get
                    (common, _) <- State.lift $ tryTc $ State.evalStateT (operandTypes lowered) query
                    maybe (traverse operandType lowered) pure common
                else traverse operandType lowered
        names <- traverse (const freshName) lowered
        environment <- queryEmbeddings
        let expression = operation (map F.EVar names)
            sorts = F.fromListSEnv (declarations ++ zip names (map (typeSort environment) types))
            checked = maybe expression (F.ECst expression) expected
        case SC.sortExprE native F.dummySpan mempty sorts checked of
            Left _ -> reject (PJ.text ("ill-sorted logical primitive application: " ++ F.showpp expression))
            Right resultSort -> do
                result <- logicalType (scopeVariables signature) resultSort
                let summary
                        | resultSort == F.boolSort = proposition expression
                        | otherwise = equality result expression
                operatorType <- case types of
                    [leftType, rightType]
                        | generalize && eqType leftType rightType ->
                            -- Equality consumes values without calling them.
                            -- Preserve ordinary polymorphic inference for a
                            -- refined callback's restricted source domain.
                            polymorphicType (typeKind leftType) (\ty -> foldr (\binder rest -> rFun binder ty rest) summary names)
                    _ -> pure (foldr (\(binder, ty) rest -> rFun binder (ofType ty) rest) summary (zip names types))
                denotation <- functionMeaning (zip names types) expression
                operator <- freshParameter operatorType denotation
                pure (foldl applyQuery operator lowered)

    conditional condition yes no = do
        condition' <- lower condition
        yes' <- lower yes
        no' <- lower no
        yesType <- operandType yes'
        noType <- operandType no'
        if eqType yesType noType
            then pure (ifQuery condition' yes' no')
            else do
                environment <- queryEmbeddings
                let sort = typeSort environment yesType
                if sort /= typeSort environment noType
                    then die "conditional branches have distinct logical sorts"
                    else do
                        carrier <- logicalType (scopeVariables signature) sort
                        yesValue <- inject carrier yesType yes'
                        noValue <- inject carrier noType no'
                        -- Keep the case: source calls inside a branch must
                        -- retain that branch's path condition during checking.
                        pure (ifQuery condition' yesValue noValue)
    -- A logical integer (literal or arithmetic result) has the canonical
    -- Integer carrier. Passing it to a source parameter of a fixed-width
    -- integral type goes through an explicit bridge whose domain is that
    -- type's target range: the conversion is an obligation, so an
    -- out-of-range value is rejected rather than assumed into a value whose
    -- type invariant contradicts it. The bridge's meaning is the identity.
    logicalInteger (F.ECst expression _) = logicalInteger expression
    logicalInteger (F.ECon F.I{}) = True
    logicalInteger F.EBin{} = True
    logicalInteger F.ENeg{} = True
    logicalInteger _ = False
    integerArgument function argument = do
        argumentType <- operandType argument
        if not (eqType argumentType integerTy)
            then pure argument
            else do
                functionType <- operandType function
                platform <- State.lift (targetPlatform <$> getDynFlags)
                case splitFunTy_maybe functionType of
                    Just (_, _, domain, _)
                        | Just constructor <- tyConAppTyCon_maybe domain
                        , Just (low, high) <- fixedWidthRange platform constructor -> do
                            let bounds = F.PAnd [F.PAtom F.Le (integerLiteral low) (F.EVar value), F.PAtom F.Le (F.EVar value) (integerLiteral high)]
                                ranged = strengthen integer (uTop (F.Reft (value, bounds)))
                            denotation <- functionMeaning [(x, integerTy)] (F.EVar x)
                            bridge <- freshParameter (rFun x ranged (equality (ofType domain) (F.EVar x))) denotation
                            pure (applyQuery bridge argument)
                    _ -> pure argument
    integerLiteral n
        | n < 0 = F.ENeg (F.ECon (F.I (negate n)))
        | otherwise = F.ECon (F.I n)

    inject carrier sourceType expression
        | eqType sourceType (specTypeToQueryType carrier) = pure expression
        | otherwise = do
            denotation <- functionMeaning [(x, sourceType)] (F.EVar x)
            bridge <- freshParameter (rFun x (ofType sourceType) (equality carrier (F.EVar x))) denotation
            pure (applyQuery bridge expression)

    -- Resolution selected the declaration's actual owner. Printed roles and
    -- equal spellings do not authorize borrowing another unit's declaration.
    isMeasure name = M.member name measureTypes
    declaration name = case M.lookup name measureTypes of
        Just (_, ty) -> (name, ty)
        Nothing -> die ("no resolved measure declaration for " ++ F.showpp name)
    selectMeasure name argument =
        let (resolved, declared) = declaration name
         in case [(receiver, ty) | (owner, receiver, ty) <- instances, owner == resolved] of
                [] -> pure declared
                [(_, ty)] -> pure ty
                candidates -> case argument of
                    Nothing -> die ("overloaded measure requires a receiver: " ++ F.showpp resolved)
                    Just receiver -> do
                        constructor <- receiverTyCon receiver
                        case [ty | (candidate, ty) <- candidates, candidate == constructor] of
                            [ty] -> pure ty
                            _ -> die ("no unique instance for the actual receiver of " ++ F.showpp resolved)

    -- This temporary query asks GHC only for a receiver's source type. It
    -- never reaches LH and contributes no facts. Nested observations have
    -- already been resolved; the final query checks their complete contracts.
    receiverTyCon argument = do
        receiver <- operandType argument
        case splitTyConApp_maybe receiver of
            Just (constructor, _) -> pure constructor
            Nothing -> die "measure receiver has no uniquely determined source type constructor"
    operandType argument = do
        types <- operandTypes [argument]
        case types of
            [ty] -> pure ty
            _ -> die "single operand probe changed its arity"
    operandTypes arguments = do
        (parameters, _, projectors) <- State.get
        probe <- freshName
        -- The marker consumes an operand at its actual runtime representation;
        -- it never binds a representation-polymorphic value in generated Core.
        unique <- State.lift getUniqueM
        let representation = mkTyVar (mkInternalName unique (mkTyVarOcc "lh_primitive_rep") noSrcSpan) runtimeRepTy
        body <- polymorphicType (mkTYPEapp (mkTyVarTy representation)) (\ty -> foldr (const (rFun x ty)) bool arguments)
        let probeType = RAllT (makeRTVar (RTV representation)) body mempty
        (elaborated, checkedType) <- State.lift $ elaborate ((probe, probeType, F.PTrue) : parameters) projectors (foldl applyQuery (variable probe) arguments)
        let core = elaborated
            actualVariables = scopeVariables (ofType (exprType core))
            sourceVariables = scopeVariables checkedType
        case withoutTypeLambdas core of
            Lam marker body -> case markerArguments marker body of
                receivers
                    | length receivers == length arguments
                    , length actualVariables == length sourceVariables ->
                        -- GHC skolems are alpha-renamed back to this query's
                        -- original telescope before separate operands are joined.
                        pure (map (substTyWith actualVariables (map mkTyVarTy sourceVariables)) receivers)
                _ -> die ("operand probe changed its scoped type-variable telescope: actual=" ++ GM.showPpr actualVariables ++ "; expected=" ++ GM.showPpr sourceVariables ++ "; markers=" ++ GM.showPpr (markerArguments marker body) ++ "; core=" ++ GM.showPpr core)
            _ -> die "receiver probe lost its scoped parameter"
    withoutTypeLambdas (Lam variable body)
        | isTyVar variable = withoutTypeLambdas body
    withoutTypeLambdas expression = expression
    markerArguments marker = go [marker]
      where
        go aliases expression
            | (Var identifier, Type _ : arguments) <- collectArgs expression
            , identifier `elem` aliases =
                map exprType (dropWhile isTypeArg arguments)
            | otherwise = case expression of
                App function argument -> go aliases function ++ go aliases argument
                Lam _ body -> go aliases body
                Let (NonRec binder (Var identifier)) body
                    | identifier `elem` aliases -> go (binder : aliases) body
                Let (NonRec _ rhs) body -> go aliases rhs ++ go aliases body
                Let (Rec bindings) body -> concatMap (go aliases . snd) bindings ++ go aliases body
                Case scrutinee _ _ alternatives -> go aliases scrutinee ++ concatMap (\(Alt _ _ body) -> go aliases body) alternatives
                Cast body _ -> go aliases body
                Tick _ body -> go aliases body
                _ -> []

    -- A measure is a logical function. Applied to a logical carrier (no
    -- source value), it is a logical primitive application: fixpoint sorts
    -- the operand's carrier against the measure's declared sort and owns the
    -- result sort, exactly as for the wired theory symbols.
    measureApplication name lowered = do
        logical <- logicalOperand lowered
        if logical
            then case F.lookupSEnv name declarations of
                Just schema -> logicalOperationOn False Nothing [(name, schema)] (apply name) [lowered]
                Nothing -> die ("no resolved measure sort for " ++ F.showpp name)
            else do
                ty <- selectMeasure name (Just lowered) >>= measureType name
                operator <- freshParameter ty (F.EVar name)
                pure (applyQuery operator lowered)
    logicalOperand lowered = do
        receiver <- operandType lowered
        local <- State.gets (\(_, current, _) -> current)
        pure (maybe False (`F.tceMember` local) (tyConAppTyCon_maybe receiver))

    measureType name declared
        | Just (T.MsReflect, _) <- M.lookup name measureTypes =
            if not (Measure.resolvedSourceInputType declared)
                then reject (PJ.text "Opaque logical observation requires a resolved source input schema")
                else
                    if Measure.supportedOpaqueResult (ty_res $ toRTypeRep declared)
                        then pure (Axiom.aty $ Axiom.addSingletonApp False name declared)
                        else reject (PJ.text "Opaque logical observation requires supported native result-domain metadata")
        | otherwise = go [] [] declared
      where
        go variables arguments (RAllT variable@(ty_var_value -> RTV tv) rest reft) =
            (\result -> RAllT variable result reft) <$> go (tv : variables) arguments rest
        go variables arguments (RFun binder info domain rest reft) =
            (\result -> RFun binder info domain result reft) <$> go variables (arguments ++ [F.EVar binder]) rest
        go variables arguments result = do
            environment <- queryEmbeddings
            let resultSort = typeSort environment (specTypeToQueryType result)
            -- `embed T as S` identifies T's values with S's: a declared
            -- embedded result is then the carrier that another measure's
            -- declared T domain consumes (Bag's `bagSize (fromList xs)`).
            -- Other results, and primitive sorts (Int-sorted results are
            -- Integer), keep their canonical logical carriers.
            carrier <- case result of
                RApp RTyCon{rtc_tc = constructor} _ _ _
                    | F.tceMember constructor embeddings
                    , resultSort `notElem` [F.boolSort, F.FInt, F.charSort, F.FReal] ->
                        pure (ofType (specTypeToQueryType result))
                _ -> logicalType variables resultSort
            pure (equality (strengthen carrier (Mb.fromMaybe mempty (stripRTypeBase result))) (apply name arguments))

    -- Preserve the declaration's input refinement before taking the actual
    -- source field. The following case (not an assumed abstract-result arrow)
    -- owns the obligation that this constructor exists on the current path.
    projectionInput (RAllT variable rest reft)
        | isTauto reft =
            (\result -> RAllT variable result reft) <$> projectionInput rest
    projectionInput (RAllP predicate rest) = RAllP predicate <$> projectionInput rest
    projectionInput (RFun binder info domain _ reft)
        | isTauto reft =
            pure (RFun binder info domain (equality domain (F.EVar binder)) reft)
    projectionInput RAllT{} = reject (PJ.text "applied projection has a refined polymorphic telescope")
    projectionInput RFun{} = reject (PJ.text "applied projection has a refined function value")
    projectionInput _ = die "source field projection requires one declared input"

    -- A first-class projection checks the actual case function against its
    -- complete declared arrow, including receiver and returned callback domains.
    projectionValue (RAllT variable rest reft)
        | isTauto reft =
            let (bridge, argument) = projectionValue rest
             in (RAllT variable bridge reft, argument)
        | otherwise = reject (PJ.text "first-class projection has a refined polymorphic telescope")
    projectionValue (RAllP predicate rest) =
        let (bridge, argument) = projectionValue rest
         in (RAllP predicate bridge, argument)
    projectionValue ty = (rFun x ty (equality ty (F.EVar x)), ty)

    projector name = do
        existing <- State.gets (\(_, _, projectors) -> L.find (\(_, _, _, meaning) -> meaning == F.EVar name) projectors)
        owner <- case existing of
            Just (owner, _, _, _) -> pure owner
            Nothing -> do
                ownerUnique <- State.lift getUniqueM
                argumentUnique <- State.lift getUniqueM
                let owner = mkInternalName ownerUnique (mkVarOcc "lh_projection") noSrcSpan
                    argumentName = mkInternalName argumentUnique (mkVarOcc "lh_projected_input") noSrcSpan
                    alternatives = projectionCases M.! name
                State.modify' (\(parameters, current, projectors) -> (parameters, current, projectors ++ [(owner, argumentName, alternatives, F.EVar name)]))
                pure owner
        pure (const (nlHsVar (nameRdrName owner)))

    lower = lowerAs Nothing
    lowerAs _ (F.ECst expression sort) = lowerAs (Just sort) expression
    lowerAs expected expression = case expression of
        F.EVar name | isSource name -> pure (variable name)
        _
            | (F.EVar name, [argument]) <- application expression
            , not (isSource name)
            , Just alternatives <- M.lookup name projectionCases -> do
                lowered <- lower argument
                logical <- logicalOperand lowered
                -- A logical receiver (e.g. a partial measure's result) has no
                -- source constructor to scrutinize; observe it logically.
                if logical
                    then measureApplication name lowered
                    else do
                        selected <- selectMeasure name (Just lowered)
                        receiver <- operandType lowered
                        input <- projectionInput selected
                        denotation <- functionMeaning [(x, receiver)] (F.EVar x)
                        bridge <- freshParameter input denotation
                        -- Eliminate this receiver in its actual scope; a generalized
                        -- helper would infer fresh, unrelated predicate parameters.
                        pure $ \locals -> nlHsCase (applyQuery bridge lowered locals) (map fieldAlternative alternatives)
        F.EVar name | M.member name projectionCases -> do
            selected <- selectMeasure name Nothing
            helper <- projector name
            let (bridgeType, argumentType) = projectionValue selected
            denotation <- functionMeaning [(x, specTypeToQueryType argumentType)] (F.EVar x)
            bridge <- freshParameter bridgeType denotation
            pure (applyQuery bridge helper)
        F.EVar name | isMeasure name -> do
            ty <- selectMeasure name Nothing >>= measureType name
            freshParameter ty (F.EVar name)
        _
            | (F.EVar name, arguments) <- application expression
            , not (isSource name)
            , Just schema <- lookup name wiredSortedSyms ->
                theory expected name schema arguments
        F.EVar name -> die ("no exact source identity or supported logical declaration for " ++ F.showpp name)
        _
            | (F.EVar name, [argument]) <- application expression
            , not (isSource name)
            , isMeasure name -> lower argument >>= measureApplication name
        F.EApp function argument -> do
            function' <- lower function
            argument' <- lower argument
            argument'' <- if logicalInteger argument then integerArgument function' argument' else pure argument'
            pure (applyQuery function' argument'')
        F.ESym{} -> logicalOperation False expected [] (const expression) []
        F.ECon F.I{} -> logicalOperation False expected [] (const expression) []
        F.ECon F.R{} -> logicalOperation False expected [] (const expression) []
        F.ECon (F.L spelling sort) | sort == F.charSort ->
            -- CoreToLogic.mkC uses canonical decimal ordinals of GHC Chars.
            -- Other raw SMT literal text has no source Char interpretation.
            case readMaybe (Text.unpack spelling) :: Maybe Integer of
                Just ordinal
                    | 0 <= ordinal && ordinal <= 0x10ffff
                    , Text.pack (show ordinal) == spelling ->
                        logicalOperation False expected [] (const expression) []
                _ -> reject (PJ.text "Invalid typed Char literal: expected a canonical decimal Unicode code point")
        F.PAtom relation left right -> logicalOperation (relation `elem` [F.Eq, F.Ne]) expected [] (\[a, b] -> F.PAtom relation a b) [left, right]
        F.EBin operator left right -> logicalOperation False expected [] (\[a, b] -> F.EBin operator a b) [left, right]
        F.ENeg argument -> logicalOperation False expected [] (\[a] -> F.ENeg a) [argument]
        F.PAnd expressions -> foldr (\e rest -> ifQuery e rest false) true <$> traverse lower expressions
        F.POr expressions -> foldr (\e rest -> ifQuery e true rest) false <$> traverse lower expressions
        F.PNot expression' -> (\e -> ifQuery e false true) <$> lower expression'
        F.PImp left right -> (\p q -> ifQuery p q true) <$> lower left <*> lower right
        F.PIff left right -> (\p q -> ifQuery p q (ifQuery q false true)) <$> lower left <*> lower right
        F.EIte condition yes no -> conditional condition yes no
        _ -> die ("unsupported logical syntax (not skipped): " ++ F.showpp expression)

    application = go []
      where
        go arguments (F.ECst expression _) = go arguments expression
        go arguments (F.EApp function argument) = go (argument : arguments) function
        go arguments function = (function, arguments)

    -- Query expressions compose directly in the lexical environment. Boolean
    -- scaffolding is expressed as cases, not overloaded source calls.
    variable name locals
        | Just local <- M.lookup name locals = nlHsVar local
        | Just identifier <- M.lookup name sourceIds = nlHsVar (nameRdrName (getName identifier))
        | otherwise = nlHsVar (varSymbolToRdrName name)
    applyQuery function argument = mkHsApp <$> function <*> argument
    ifQuery condition yes no = nlHsIf <$> condition <*> yes <*> no
    true = const (nlHsVar true_RDR)
    false = const (nlHsVar (getRdrName falseDataCon))
    bindProjector (owner, argumentName, alternatives, _) expression =
        let helper = nameRdrName owner
            parameter = nameRdrName argumentName
            body = nlHsCase (nlHsVar parameter) (map fieldAlternative alternatives)
            binding = mkSimpleGeneratedFunBind noSrcSpan helper (noLocA [nlVarPat parameter]) body
            bindings = HsValBinds noAnn (ValBinds mempty [binding] [])
         in noLocA (HsLet (noAnn, noAnn) bindings expression)
    fieldAlternative (constructor, index) =
        mkSimpleMatch CaseAlt (noLocA [pattern]) (nlHsVar selected)
      where
        selected = mkRdrUnqual (mkVarOcc "lh_selected_field")
        pattern =
            nlConPat
                (getRdrName constructor)
                [if field == index then nlVarPat selected else nlWildPat | field <- [0 .. length (dataConOrigArgTys constructor) - 1]]

-- The query is checked in its source telescope, not RefType.toType's logical
-- erasure: keep implicit quantification, original variable identities and
-- dependent kinds. Class arguments remain givens, not ordinary value arrows.
-- Existential evidence does not change a value's source type. Its lexical
-- scope is opened as an explicit query binder when checking its body below.
elaborateSpecType' ::
    (Type -> SpecType -> F.Expr -> TcRn T.CheckedPredicate) ->
    (T.CheckedPredicate -> TcRn ()) ->
    (SpecType -> SpecType) ->
    SpecType ->
    TcRn T.CheckedSpecType
-- The context has exactly one hole: the result of the enclosing telescope.
-- Every query interprets its own checked binders, so sibling types need no
-- reconciliation of GHC-generated dictionary names.
elaborateSpecType' query collect scope t =
    case t of
        RVar variable reft -> refine (reft, t) (RVar variable)
        RFun binder info domain result reft -> do
            domain' <- elaborateSpecType' query collect scope domain
            result' <- elaborateSpecType' query collect (scope . (\rest -> RFun binder info (T.ordinarySpecType domain') rest reft)) result
            refine (reft, RFun binder info (T.ordinarySpecType domain') (T.ordinarySpecType result') reft) (RFun binder info domain' result')
        RAllT variable rest reft -> do
            rest' <- elaborateSpecType' query collect (scope . (\result -> RAllT variable result reft)) rest
            refine (reft, RVar (ty_var_value variable) mempty) (RAllT variable rest')
        RAllP predicate rest ->
            RAllP predicate <$> elaborateSpecType' query collect (scope . RAllP predicate) rest
        RApp constructor arguments predicates reft
            | isClass constructor -> pure (T.logicalSpecType t)
            | otherwise -> do
                arguments' <- traverse (elaborateSpecType' query collect scope) arguments
                predicates' <- traverse elaborateProperty predicates
                refine (reft, RApp constructor (map T.ordinarySpecType arguments') (map (fmap T.ordinarySpecType) predicates') reft) (RApp constructor arguments' predicates')
        RAppTy function argument reft -> do
            function' <- elaborateSpecType' query collect scope function
            argument' <- elaborateSpecType' query collect scope argument
            refine (reft, RAppTy (T.ordinarySpecType function') (T.ordinarySpecType argument') reft) (RAppTy function' argument')
        -- A witness scopes over the predicate, not the represented calling convention.
        REx binder witness rest -> do
            witness' <- elaborateSpecType' query collect scope witness
            rest' <- elaborateSpecType' query collect (scope . (\result -> RFun binder defRFInfo (T.ordinarySpecType witness') result mempty)) rest
            pure (REx binder witness' rest')
        RLit literal -> pure (RLit literal)
        RExprArg _ -> impossible Nothing "RExprArg should not appear here"
        RHole _ -> impossible Nothing "RHole should not appear here"
        RRTy environment reft OCons rest ->
            RRTy <$> elaborateConstraint scope environment <*> pure (T.CheckedRefinement reft []) <*> pure OCons <*> elaborateSpecType' query collect scope rest
        RRTy{} -> todo Nothing ("Not sure how to elaborate RRTy" ++ F.showpp t)
  where
    elaborateProperty (RProp binders body@RHole{}) = pure (RProp binders (T.logicalSpecType body))
    elaborateProperty (RProp binders body) =
        RProp binders <$> elaborateSpecType' query collect (scope . propertyContext) body
      where
        propertyContext result = foldr (\(owner, carrier) rest -> RFun owner defRFInfo (ofRSort carrier) rest mempty) result binders

    -- OCons stores a lexical context followed by two subtype endpoints.
    -- Its context scopes over those endpoints, independently of the payload.
    elaborateConstraint context [(left, lhs), (right, rhs)] =
        (\lhs' rhs' -> [(left, lhs'), (right, rhs')])
            <$> elaborateSpecType' query collect context lhs
            <*> elaborateSpecType' query collect context rhs
    elaborateConstraint context ((binder, domain) : rest) = do
        domain' <- elaborateSpecType' query collect context domain
        rest' <- elaborateConstraint (context . (\result -> RFun binder defRFInfo (T.ordinarySpecType domain') result mempty)) rest
        pure ((binder, domain') : rest')
    elaborateConstraint _ [] = impossible Nothing "Subtype obligation has fewer than two endpoints"

    boolType = RApp (RTyCon boolTyCon [] defaultTyConInfo) [] [] mempty :: SpecType
    refine (original@(MkUReft (F.Reft (value, predicate)) abstract), valueType) rebuild
        -- Inference placeholders have no source predicate to elaborate.
        | T.isHole predicate || predicate == F.PTrue = pure (rebuild (T.CheckedRefinement original []))
        | otherwise = do
            let originalQuery = scope (rFun' (classRFInfo True) value valueType boolType)
                occupied = querySourceSymbols originalQuery `S.union` F.syms predicate
                (_, queryValue) = F.freshInNS value occupied
                queryType = scope (rFun' (classRFInfo True) queryValue valueType boolType)
            checked <- query (specTypeToQueryType boolType) (eraseCheckedRefinement queryType) (F.subst1 predicate (value, F.EVar queryValue))
            resident <- case renameCheckedPredicateOwner (specTypeToQueryType valueType) queryValue value checked of
                Left message -> do
                    location <- getSrcSpanM
                    uError (ErrTySpec location (Just "refinement formation") "refinement" (F.pprint queryType) (PJ.text message))
                Right renamed -> pure renamed
            collect resident
            pure (rebuild (T.CheckedRefinement (MkUReft (F.Reft (value, F.PTrue)) abstract) [resident]))

    eraseCheckedRefinement (RAllT variable rest reft) = RAllT variable (eraseCheckedRefinement rest) reft
    eraseCheckedRefinement (RAllP predicate rest) = RAllP predicate (eraseCheckedRefinement rest)
    eraseCheckedRefinement (RFun binder info domain result reft)
        | hasValueArgument result = RFun binder info domain (eraseCheckedRefinement result) reft
        | otherwise =
            RFun
                binder
                info
                (eraseRootContract domain)
                (eraseRootContract result)
                reft
    eraseCheckedRefinement ty = eraseRootContract ty

    -- Formation cannot assume the concrete predicate being established. The
    -- independent abstract membership and child contracts still determine
    -- where that source predicate must be admitted.
    eraseRootContract :: SpecType -> SpecType
    eraseRootContract ty =
        strengthenWith
            (\original _ -> original{ur_reft = F.Reft (F.reftBind $ ur_reft original, F.PTrue)})
            ty
            mempty

    hasValueArgument (RAllT _ rest _) = hasValueArgument rest
    hasValueArgument (RAllP _ rest) = hasValueArgument rest
    hasValueArgument RFun{} = True
    hasValueArgument _ = False

-- | Embed fixpoint expressions into parsed haskell expressions.
--   It allows us to bypass the GHC parser and use arbitrary symbols
--   for identifiers (compared to using the string API)
symbolToRdrNameNs :: NameSpace -> F.Symbol -> RdrName
symbolToRdrNameNs ns x
  | F.isNonSymbol modName = mkUnqual ns (mkFastString (F.symbolString s))
  | otherwise = mkQual
    ns
    (mkFastString (F.symbolString modName), mkFastString (F.symbolString s))
  where (modName, s) = GM.splitModuleName x


varSymbolToRdrName :: F.Symbol -> RdrName
varSymbolToRdrName = symbolToRdrNameNs varName
