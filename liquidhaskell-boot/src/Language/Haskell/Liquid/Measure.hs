{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE TypeOperators          #-}

module Language.Haskell.Liquid.Measure (
  -- * Specifications
    Spec (..)
  , MSpec (..)

  -- * Type Aliases
  , BareSpec
  , BareMeasure
  , SpecMeasure

  -- * Constructors
  , mkM, mkMSpec, mkMSpec'
  , checkDuplicateMeasure
  , dataConTypes
  , measureInputType
  , sourceInputType
  , resolvedSourceInputType
  , supportedOpaqueResult
  , ConstructorBox
  , makeConstructorBox
  , makeConstructorBoxes
  , constructorSourceFields
  , constructorWorkerType
  , constructorSourceMatch
  , definitionFits
  , definitionFitsInput
  , instantiateConstructorEquation
  , deferredConstructorEquation
  , constructorEquationSchemas
  , defRefType
  , bodyPred
  ) where

import           GHC                                    hiding (Located)
import           Prelude                                hiding (error)
import           Text.PrettyPrint.HughesPJ              hiding ((<>))
-- import           Data.Binary                            as B
-- import           GHC.Generics
import qualified Data.HashMap.Strict                    as M
import qualified Data.HashSet                           as S
import qualified Language.Haskell.Liquid.Types.Visitors as V
import qualified GHC.Core as C
import qualified GHC.Core.DataCon as C
import qualified GHC.Core.Coercion as C
import qualified GHC.Core.Subst as C
import qualified GHC.Core.Type as C
import qualified GHC.Core.Unify as C
import qualified GHC.Core.Utils as C
import qualified GHC.Data.FastString as C
import qualified GHC.Types.Id as C
import qualified GHC.Types.Id.Make as C
import qualified GHC.Types.Unique.Supply as C
import qualified GHC.Types.Var.Env as C
import qualified GHC.Types.Var.Set as C
import qualified Data.List                              as L
import qualified Data.Maybe                             as Mb -- (fromMaybe, isNothing)
import GHC.Stack
import Control.Monad (foldM, guard)

import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types                as F hiding (panic, R, DataDecl, SrcSpan, LocSymbol)
import qualified Language.Fixpoint.Types.Visitor as Visitor
import           Liquid.GHC.API        as Ghc hiding (Expr, showPpr, panic, (<+>))
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.RefType
-- import           Language.Haskell.Liquid.Types.Variance
-- import           Language.Haskell.Liquid.Types.Bounds
import           Language.Haskell.Liquid.Types.Specs
import           Language.Haskell.Liquid.UX.Tidy


mkM :: HasCallStack => F.Located LHName -> ty -> [DefV v ty bndr] -> MeasureKind -> UnSortedExprs -> MeasureV v ty bndr
mkM name typ eqns kind u
  | all ((name ==) . measure) eqns
  = M name typ eqns kind u
  | otherwise
  = panic Nothing $ "invalid measure definition for " ++ show name

mkMSpec' :: [Measure ty DataCon] -> MSpec ty DataCon
mkMSpec' ms = MSpec cm mm M.empty []
  where
    cm     = groupMap (makeGHCLHNameFromId . dataConWorkId . ctor) $ concatMap msEqns ms
    mm     = M.fromList [(msName m, m) | m <- ms ]

-- Note [Duplicate measures and opaque reflection]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Note that only ms are checked for duplicates! `oms` are the opaque reflections, they are automatically generated
-- so we don't care about duplicates (any two opaque-reflection measures with the same name will refer to the same thing,
-- since their names are fully qualified). Whence the need for a separate field for opaque reflections vs usual measures.
mkMSpec :: [Measure t (F.Located LHName)] -> [Measure t ()] -> [Measure t (F.Located LHName)] -> [Measure t (F.Located LHName)] -> MSpec t (F.Located LHName)
mkMSpec ms cms ims oms = MSpec cm mm cmm ims
  where
    cm     = groupMap (val . ctor) $ concatMap msEqns (ms'++ims)
    mm     = M.fromList [(msName m, m) | m <- ms' ]
    cmm    = M.fromList [(msName m, m) | m <- cms ]
    ms'    = checkDuplicateMeasure ms ++ oms


checkDuplicateMeasure :: [Measure ty ctor] -> [Measure ty ctor]
checkDuplicateMeasure measures
  = case M.toList dups of
      []         -> measures
      (m,ms):_   -> uError $ mkError m (msName <$> ms)
    where
      gms        = group [(msName m , m) | m <- measures]
      dups       = M.filter ((1 <) . length) gms
      mkError m ms = ErrDupMeas (fSrcSpan m) (pprint (val m)) (fSrcSpan <$> ms)


-- Retain only the source input contract, with the same leading-evidence
-- projection as CoreToLogic.logicType. Claimed result facts are not equations.
measureInputType :: SpecType -> SpecType
measureInputType ty =
    fromRTypeRep rep{ty_binds = names, ty_info = infos, ty_args = args, ty_refts = refts}
  where
    rep = toRTypeRep (inputOnly ty)
    erasable = isEmbeddedClass
    (names, infos, args, refts) =
        L.unzip4 $
            dropWhile (\(_, _, input, _) -> erasable input) $
                L.zip4 (ty_binds rep) (ty_info rep) (ty_args rep) (ty_refts rep)
    inputOnly (RAllT a t _) = RAllT a (inputOnly t) mempty
    inputOnly (RAllP p t) = RAllP p (inputOnly t)
    inputOnly (RFun x i input result _) = RFun x i input (inputOnly result) mempty
    inputOnly t = fmap (const mempty) t

-- Retain the full native input/evidence telescope. Nested result contracts
-- are deliberately retained as metadata, not silently weakened: consumers
-- without the source owner must reject unsupported result-domain structure.
sourceInputType :: SpecType -> SpecType
sourceInputType (RAllT a t _) = RAllT a (sourceInputType t) mempty
sourceInputType (RAllP p t) = RAllP p (sourceInputType t)
sourceInputType (RFun x i input result _) = RFun x i input (sourceInputType result) mempty
sourceInputType t = topRTypeBase t

resolvedSourceInputType :: SpecType -> Bool
resolvedSourceInputType ty =
    not (hasHoleTy ty) && foldReft False closed True ty
  where
    closed _ refinement rest =
        rest && not (hasHole refinement) && null (Visitor.kvarsExpr $ F.reftPred $ toReft refinement)

-- Refined result parameters can occur contravariantly in constructor fields.
-- Neither erasing nor retaining them is a domain-only projection in general.
supportedOpaqueResult :: SpecType -> Bool
supportedOpaqueResult result =
    case result of
        RApp{} -> isTrivial result
        RAppTy{} -> isTrivial result
        RVar{} -> isTrivial result
        RLit{} -> True
        _ -> False

{- | Returns the specification types of all data constructors augmented with
the refinements from the measures. Also returns the specification types of
the measures in the second component of the result.
-}
dataConTypes :: (CoreExpr -> (F.Expr, LogicSupport)) -> M.HashMap DataCon ConstructorBox -> Bool -> MSpec (RRType Reft) DataCon -> (([(Var, RRType Reft)], [(F.Located LHName, RRType Reft)]), LogicSupport)
dataConTypes interpret boxes allowTC s = ((concat ctorTys, measTys), concat support)
  where
    measTys = [(msName m, msSort m) | m <- M.elems (measMap s) ++ imeas s]
    (ctorTys, support) = unzip $ map (makeDataConType interpret boxes allowTC domains . notracepp "HOHOH" . snd) (M.toList (ctorMap s))

    domains =
        M.fromList
            [ (val (msName m), inputDomain (msSort m))
            | m <- M.elems (measMap s) ++ imeas s
            , msKind m == MsLifted
            ]
    -- As with source measure admission, only complete scalar input membership
    -- is interpreted here. Unsupported input structure yields no equation.
    inputDomain :: RRType Reft -> Reft
    inputDomain ty = case ty_args (toRTypeRep ty) of
        [input] | isBase input && isTrivial (topRTypeBase input) -> rTypeReft input
        _ -> Reft (F.vv_, PFalse)

makeDataConType :: (CoreExpr -> (F.Expr, LogicSupport)) -> M.HashMap DataCon ConstructorBox -> Bool -> M.HashMap LHName Reft -> [Def (RRType Reft) DataCon] -> ([(Var, RRType Reft)], LogicSupport)
makeDataConType _ _ _ _ [] =
  ([], [])
makeDataConType _ _ allowTC domains ds
  | Mb.isNothing (dataConWrapId_maybe dc) =
      (notracepp _msg [(woId, notracepp _msg $ combineDCTypes "cdc0" t ts)], [])
 where
  dc = ctor (head ds)
  woId = dataConWorkId dc
  t = varType woId
  ts = [defRefType allowTC (M.lookup (val (measure d)) domains) t d | d <- ds]
  _msg = "makeDataConType0" ++ showpp (woId, t, ts)
makeDataConType interpret boxes allowTC domains ds =
  (rows, retainLogicSupport (S.unions $ map (F.syms . snd) rows) (concat support ++ identitySupport))
 where
  rows = [(woId, noDummySyms woIdentity), (wrId, noDummySyms wrIdentity)]
  (woIdentity, identitySupport) = sourceIdentity True woRType
  (wrIdentity, _) = sourceIdentity False wrRType
  -- Parsed/generated equations describe source fields; lifted Core equations
  -- retain their actual case-binder carriers. A worker equation is not a
  -- wrapper equation when those carriers differ.
  (wo, support) = unzip $ map (workerDefinition interpret boxes) ds
  wr = filter (definitionFits wrt) ds
  dc = ctor $ head ds
  woId = dataConWorkId dc
  wot = varType woId
  wrId = dataConWrapId dc
  wrt = varType wrId
  wots = [defRefType allowTC (M.lookup (val (measure d)) domains) wot d | d <- wo]
  wrts = [defRefType allowTC (M.lookup (val (measure d)) domains) wrt d | d <- wr]

  wrRType = combineDCTypes "cdc1" wrt wrts
  woRType = combineDCTypes "cdc2" wot wots
  sourceIdentity workerSide t = (fromRTypeRep rep{ty_res = ty_res rep `strengthen` F.exprReft image}, retained)
   where
    rep = toRTypeRep t
    arguments = [F.EVar x | (x, a) <- zip (ty_binds rep) (ty_args rep), not (isEmbeddedDictType (toType False a))]
    (image, retained)
      | not workerSide = (F.mkEApp (namedLocSymbol dc) arguments, [])
      | Just (ConstructorBox worker sources) <- M.lookup dc boxes
      , let values = filter (not . isEmbeddedDictType . varType) worker
      , length values == length arguments =
          let su = F.mkSubst (zip (map F.symbol values) arguments)
              (fields, dependencies) = unzip [interpret e | (v, e) <- sources, not (isEmbeddedDictType (varType v))]
           in (F.mkEApp (namedLocSymbol dc) (map (F.subst su) fields), concat dependencies)
      | otherwise = panicDataCon (getSrcSpan dc) dc (Text.PrettyPrint.HughesPJ.text "missing source constructor identity reconstruction")

-- The actual GHC boxer owns the worker telescope and each source expression.
-- Core types and coercions survive until the existing logical interpretation.
makeConstructorBoxes :: (C.MonadUnique m) => [DataCon] -> m (M.HashMap DataCon ConstructorBox)
makeConstructorBoxes = go M.empty
  where
    go boxes [] = pure boxes
    go boxes (dc : rest)
        | M.member dc boxes = go boxes rest
        | otherwise = do
            box@(ConstructorBox _ fields) <- makeConstructorBox dc
            let nested = [inner | (_, e) <- fields, v <- V.readVars e, isId v, DataConWorkId inner <- [idDetails v]]
                newtypes =
                    [ inner
                    | (_, e) <- fields
                    , Just (tc, _) <- [splitTyConApp_maybe (C.exprType e)]
                    , isNewTyCon tc
                    , inner <- tyConDataCons tc
                    ]
            -- Declaring a datatype declares all its constructors, including
            -- unused siblings whose unpacked fields also need reconstruction.
            go (M.insert dc box boxes) (tyConDataCons (dataConTyCon dc) ++ nested ++ newtypes ++ rest)

makeConstructorBox :: C.MonadUnique m => DataCon -> m ConstructorBox
makeConstructorBox dc = do
  sources <- mapM sourceVariable sourceTypes
  supply <- C.getUniqueSupplyM
  let C.DCB boxer = Mb.fromMaybe C.vanillaDataConBoxer (C.dataConBoxer dc)
      (allWorker, bindings) = C.initUs_ supply (boxer (map mkTyVarTy universals) (existentials ++ sources))
      worker = drop (length existentials) allWorker
      expected = map irrelevantMult (C.dataConRepArgTys dc)
      expressions = map (rebuild bindings . C.varToCoreExpr) sources
  if length worker == length expected
     && and (zipWith (\v ty -> eqType (varType v) ty) worker expected)
     && and (zipWith (\v e -> eqType (varType v) (C.exprType e)) sources expressions)
    then pure (ConstructorBox worker (zip sources expressions))
    else panicDataCon (getSrcSpan dc) dc (Text.PrettyPrint.HughesPJ.text "GHC boxer disagrees with constructor carriers")
  where
    (universals, existentials, equalities, context, fields, _) = dataConFullSig dc
    sourceTypes = C.eqSpecPreds equalities ++ context ++ map irrelevantMult fields
    sourceVariable ty = do
      unique <- C.getUniqueM
      pure (C.mkSysLocalOrCoVar (C.fsLit "lh_source") unique C.ManyTy ty)
    rebuild bindings expression = foldr substitute expression bindings
    substitute (C.Rec _) _ = panicDataCon (getSrcSpan dc) dc (Text.PrettyPrint.HughesPJ.text "recursive GHC boxer binding")
    substitute (C.NonRec binder rhs) expression =
      let scope = C.mkInScopeSet (exprFreeVars rhs `C.unionVarSet` exprFreeVars expression)
          initial = C.mkEmptySubst scope
          substitution = case rhs of
            C.Type ty | isTyVar binder -> C.extendTvSubst initial binder ty
            C.Coercion co | isCoVar binder -> C.extendCvSubst initial binder co
            _ -> C.extendIdSubst initial binder rhs
      in C.substExpr substitution expression

-- Instantiate the actual boxer at an actual Core alternative. Existential
-- type/coercion binders precede worker values and retain their GHC ownership.
constructorSourceFields :: M.HashMap DataCon ConstructorBox -> DataCon -> Type -> [CoreExpr] -> Maybe [CoreExpr]
constructorSourceFields boxes dc result actual = do
    ConstructorBox worker sources <- M.lookup dc boxes
    let sourceResult = sourceFamily result
        representationResult = C.mkFamilyTyConApp (dataConTyCon dc) (map mkTyVarTy (dataConUnivTyVars dc))
    initial <- C.tcMatchTy representationResult sourceResult
    let existentials = C.dataConExTyCoVars dc
        (actualExistentials, actualWorker) = splitAt (length existentials) actual
        scope =
            C.mkInScopeSet
                ( C.unionVarSets (map exprFreeVars actual)
                    `C.unionVarSet` C.tyCoVarsOfType result
                    `C.unionVarSet` C.unionVarSets (map (exprFreeVars . snd) sources)
                )
        extend substitution (variable, argument) = C.extendSubst substitution variable argument
        types = L.foldl' extend (C.setInScope initial scope) (zip existentials actualExistentials)
        substitution = L.foldl' extend types (zip worker actualWorker)
        expressions = map (C.substExpr substitution . snd) sources
        sameType substitution' expected observed =
            category expected observed
                && eqType (C.substTy substitution' (varType expected)) (argumentType observed)
    if length actualExistentials == length existentials
        && length actualWorker == length worker
        && and (zipWith (sameType types) existentials actualExistentials)
        && and (zipWith (sameType types) worker actualWorker)
        && and (zipWith (\(source, _) expression -> eqType (C.substTy types (varType source)) (C.exprType expression)) sources expressions)
        then Just expressions
        else Nothing
  where
    category variable (C.Type _) = isTyVar variable
    category variable (C.Coercion _) = isCoVar variable
    category variable _ = isId variable && not (isCoVar variable)
    argumentType (C.Type ty) = C.typeKind ty
    argumentType (C.Coercion co) = C.coercionType co
    argumentType expression = C.exprType expression

-- Match the complete source telescope jointly, including its result. Bound
-- type variables may be renamed, not specialized; nominal field constructors
-- and repeated variable associations retain their GHC meaning. Compare both
-- sides through the existing runtime refinement-type projection: RType does
-- not represent GHC arrow flags or forall visibility, but False retains every
-- runtime dictionary input, including under nested polymorphic fields.
constructorSourceMatch :: DataCon -> SpecType -> Maybe C.Subst
constructorSourceMatch dc sourceType = do
    let source = toRTypeRep sourceType
        declared = [variable | (binder, _) <- ty_vars source, let RTV variable = ty_var_value binder]
        (bound, arguments, result) = splitType (varType (dataConWrapId dc))
        actual = filter isTyVar bound
        carrier = map (toType False) (ty_args source) ++ [toType False (ty_res source)]
    if length arguments /= length (ty_args source) || length declared /= length actual
        then Nothing
        else do
            substitution <- C.tcMatchTys carrier (map runtimeCarrier (arguments ++ [result]))
            selected <- traverse (C.getTyVar_maybe . C.substTy substitution . mkTyVarTy) declared
            if selected == actual
                then Just substitution
                else Nothing

runtimeCarrier :: Type -> Type
runtimeCarrier ty = toType False (ofType ty :: SpecType)

-- Pull a source constructor contract back along GHC's typed reconstruction.
-- Every source input predicate and the result use the same substitution. Input
-- membership is checked at the last worker value, where all fields are in scope;
-- it is not discarded or asserted as an unconditional property of the result.
constructorWorkerType :: (CoreExpr -> (F.Expr, LogicSupport)) -> M.HashMap DataCon ConstructorBox -> DataCon -> SpecType -> (SpecType, LogicSupport)
constructorWorkerType interpret boxes dc sourceType
    | not (null (ty_preds source)) = reject "abstract source predicates require checked worker transport"
    | not (all isTauto (ty_refts source ++ map snd (ty_vars source))) = reject "refined source arrows require checked worker transport"
    | Just (ConstructorBox worker fields) <- M.lookup dc boxes
    , length worker == length (ty_args target)
    , and (zipWith (\v t -> eqType (runtimeCarrier (varType v)) (toType False t)) worker (ty_args target))
    , length fields == length (ty_args source)
    , and (zipWith (\(v, _) t -> eqType (runtimeCarrier (varType v)) (toType False t)) fields (ty_args source))
    , eqType (toType False (ty_res source)) (toType False (ty_res target)) =
        if all supported (ty_args source)
            then
                let occupied = S.fromList (ty_binds source) `S.union` F.syms sourceType
                    (_, names) = F.freshInNSL (map F.symbol worker) occupied
                    leaves = F.mkSubst (zip (map F.symbol worker) (map F.EVar names))
                    (meanings, dependencies) = unzip $ map (interpret . snd) fields
                    rebuilt = map (F.subst leaves) meanings
                    substitution = F.mkSubst (zip (ty_binds source) rebuilt)
                    membership t expression =
                        let F.Reft (value, predicate) = rTypeReft t
                         in F.subst substitution (F.subst (F.mkSubst [(value, expression)]) predicate)
                    domain = F.pAnd (zipWith membership (ty_args source) rebuilt)
                    arguments = ty_args target
                    result = F.subst substitution (ty_res source)
                    requireLast = reverse (requireValue (reverse (zip names arguments)))
                    requireValue []
                        | F.isTautoPred domain = []
                        | otherwise = reject "source input predicates have no worker value boundary"
                    requireValue (pair@(name, argument) : rest)
                        | isEmbeddedDictType (toType False argument) = pair : requireValue rest
                        | any (`S.member` F.syms domain) (map fst (takeWhile (isEmbeddedDictType . toType False . snd) (reverse (zip names arguments)))) =
                            reject "source input predicates use later worker evidence"
                        | otherwise = (name, argument `strengthen` MkUReft (F.Reft (name, domain)) mempty) : rest
                    transported = fromRTypeRep target{ty_binds = map fst requireLast, ty_args = map snd requireLast, ty_res = result}
                 in (transported, retainLogicSupport (F.syms transported) (concat dependencies))
            else reject "non-scalar source fields require checked worker transport"
    | otherwise = reject "missing or incompatible GHC source reconstruction"
  where
    source = case constructorSourceMatch dc sourceType of
        Nothing -> reject "source constructor contract does not match GHC carrier"
        Just substitution ->
            let representation = toRTypeRep sourceType
                replacements =
                    [ (variable, toRSort replacement, replacement)
                    | (binder, _) <- ty_vars representation
                    , let variable@(RTV ghcVariable) = ty_var_value binder
                          replacement = ofType (C.substTy substitution (mkTyVarTy ghcVariable))
                    ]
                align = subsTyVarsMeet replacements
             in representation{ty_args = map align (ty_args representation), ty_res = align (ty_res representation)}
    target = toRTypeRep (ofType (varType (dataConWorkId dc)))
    supported t = scalarRoot t && isBase t && isTrivial (topRTypeBase t) && null (pvars (ur_pred (Mb.fromMaybe mempty (stripRTypeBase t))))
    scalarRoot RVar{} = True
    scalarRoot RApp{} = True
    scalarRoot RAppTy{} = True
    scalarRoot RLit{} = True
    scalarRoot _ = False
    reject message = panicDataCon (getSrcSpan dc) dc (Text.PrettyPrint.HughesPJ.text message)

workerDefinition :: (CoreExpr -> (F.Expr, LogicSupport)) -> M.HashMap DataCon ConstructorBox
                 -> Def (RRType Reft) DataCon -> (Def (RRType Reft) DataCon, LogicSupport)
workerDefinition interpret boxes definition@(Def f dc mt xs body)
  | eqType (varType (dataConWorkId dc)) (varType (dataConWrapId dc)) = (definition, [])
  | all (Mb.isJust . snd) xs
  , definitionFits (varType (dataConWorkId dc)) definition = (definition, [])
  | not (all (maybe True (all isTauto) . snd) xs) =
      reject "refined source fields require checked worker transport"
  | Just (ConstructorBox worker sources) <- M.lookup dc boxes
  , let logicalWorker = filter (not . evidence . varType) worker
  , let logicalSources = filter (not . evidence . varType . fst) sources
  , length logicalSources == length xs
  , and (zipWith sameSourceCarrier xs logicalSources) =
      let occupied = S.fromList (map fst xs) `S.union` F.syms body
          (_, names) = F.freshInNSL (map F.symbol logicalWorker) occupied
          leaves = F.mkSubst (zip (map F.symbol logicalWorker) (map EVar names))
          (meanings, dependencies) = unzip $ map (interpret . snd) logicalSources
          fields = map (F.subst leaves) meanings
      in (Def f dc mt (map (, Nothing) names) (F.subst (F.mkSubst (zip (map fst xs) fields)) body), concat dependencies)
  | otherwise = reject "missing or incompatible GHC source reconstruction"
  where
    evidence = isEmbeddedDictType
    reject message = panicDataCon (fSrcSpan f) dc (Text.PrettyPrint.HughesPJ.text (message ++ details))
    details = "; equation fields=" ++ show (map (maybe "<untyped>" (showPpr . toType False) . snd) xs)
      ++ "; result=" ++ maybe "<untyped>" (showPpr . toType False) mt
      ++ case M.lookup dc boxes of
           Nothing -> "; boxer absent"
           Just (ConstructorBox worker sources) ->
             "; source fields=" ++ show (map (showPpr . varType . fst) (filter (not . evidence . varType . fst) sources))
             ++ "; worker fields=" ++ show (map (showPpr . varType) (filter (not . evidence . varType) worker))
    sameSourceCarrier (_, annotation) (source, _) =
      maybe True (\ty -> eqType (toType False ty) (varType source)) annotation

-- Match the complete observed carrier jointly, retaining repeated type-variable
-- associations. This classifies an equation; it does not erase its refinements.
definitionFits :: Type -> Def (RRType Reft) DataCon -> Bool
definitionFits target = Mb.isJust . definitionMatch target

-- The declaration and every retained equation observation must admit the same
-- constructor instantiation; matching them independently loses correlations.
definitionFitsInput :: Type -> Type -> Def (RRType Reft) DataCon -> Bool
definitionFitsInput input target = Mb.isJust . definitionMatchWith (Just input) target

definitionMatch :: Type -> Def (RRType Reft) DataCon -> Maybe C.Subst
definitionMatch = definitionMatchWith Nothing

definitionMatchWith :: Maybe Type -> Type -> Def (RRType Reft) DataCon -> Maybe C.Subst
definitionMatchWith input target definition = do
    observations <- definitionObservations input target definition
    C.tcMatchTys (map (sourceFamily . fst) observations) (map (sourceFamily . snd) observations)

definitionObservations :: Maybe Type -> Type -> Def (RRType Reft) DataCon -> Maybe [(Type, Type)]
definitionObservations input target (Def _ _ result fields _)
    | length arguments == length logicalFields =
        Just observations
    | otherwise = Nothing
  where
    (_, allArguments, targetResult) = splitType target
    evidence = isEmbeddedDictType
    arguments = filter (not . evidence) allArguments
    logicalFields = filter (not . maybe False (evidence . toType False) . snd) fields
    observations =
        [(expected, toType False actual) | (expected, (_, Just actual)) <- zip arguments logicalFields]
            ++ maybe [] (\actual -> [(targetResult, toType False actual)]) result
            ++ maybe [] (\actual -> [(targetResult, actual)]) input

sourceFamily :: Type -> Type
sourceFamily ty = maybe ty (uncurry C.mkFamilyTyConApp) (C.splitTyConApp_maybe ty)

-- A supported authored equation can be well formed at its declared carrier
-- without being uniformly applicable to the constructor's rigid generic
-- carrier. Keep that original equation for admission and scoped use, rather
-- than putting a specialized refinement on the generic constructor or PLE rule.
-- Unsupported functional/evidence schemas keep their existing interpretation.
constructorEquationSchemas :: MSpec SpecType DataCon -> MSpec SpecType DataCon
constructorEquationSchemas declarations = declarations{ctorMap = M.map (filter (not . deferred)) (ctorMap declarations)}
  where
    signatures = M.fromList [(val (msName m), m) | m <- M.elems (measMap declarations) ++ imeas declarations]
    deferred definition = case M.lookup (val (measure definition)) signatures of
        Just declaration | msKind declaration == MsMeasure -> deferredConstructorEquation (msSort declaration) definition
        _ -> False

deferredConstructorEquation :: SpecType -> Def SpecType DataCon -> Bool
deferredConstructorEquation signature definition = case ty_args (toRTypeRep signature) of
    [input]
        | not (isNewTyCon (dataConTyCon dc))
        , Ghc.dataConWrapperType dc `eqType` varType (dataConWorkId dc)
        , all (foldReft False (\_ reft admissible -> ur_pred reft == mempty && admissible) True) [ty | Just ty <- dsort definition : map snd (binds definition)]
        , Just substitution <- definitionMatchWith (Just (toType False input)) generic original
        , let selected = C.substTy substitution generic
        , Mb.isJust (instantiateConstructorEquation signature selected original) ->
            Mb.isNothing (instantiateConstructorEquation signature generic original)
    _ -> False
  where
    dc = ctor definition
    original = mapDefTy (fmap toReft) definition
    (_, arguments, result) = splitType (Ghc.dataConWrapperType dc)
    generic = C.mkVisFunTysMany arguments result

-- Scoped equation instantiation. Only constructor and
-- declaration-owned ordinary forall binders are flexible, after independent
-- capture-safe freshening. Actual source coordinates and unowned observations
-- remain rigid. Input and observed refinements are PREMISES, not new facts.
-- Unsupported nested domains, higher-rank inputs and evidence return Nothing.
-- The returned receiver refinement still requires the original field scope.
instantiateConstructorEquation :: SpecType -> Type -> Def (RRType Reft) DataCon -> Maybe (RRType Reft)
instantiateConstructorEquation signature actual definition@(Def name dc metadata fields body) = do
    input <- case ty_args declaration of
        [first] -> do
            guard (foldReft False (\_ reft admissible -> ur_pred reft == mempty && admissible) True first)
            Just (fmap toReft first)
        _ -> Nothing
    guard (null (ty_preds declaration) && all (isTauto . snd) (ty_vars declaration))
    guard (all (not . isEmbeddedClass) (ty_args declaration))
    guard (all isTyVar (constructorVariables ++ measureVariables ++ actualVariables))
    guard (all isBaseTy (arguments ++ actualArguments))
    guard (all (\ty -> not (isEmbeddedDictType ty) && not (isEmbeddedClass (ofType ty :: SpecType))) (arguments ++ actualArguments))
    let originalTypes =
            arguments
                ++ [result, toType False input]
                ++ actualArguments
                ++ [actualResult]
                ++ [toType False ty | Just ty <- metadata : map snd fields]
        occupied = C.mkInScopeSet (C.tyCoVarsOfTypes originalTypes `C.unionVarSet` C.mkVarSet (constructorVariables ++ measureVariables))
        (constructorRename, freshConstructorVariables) = C.substTyVarBndrs (C.mkEmptySubst occupied) constructorVariables
        (measureRename, freshMeasureVariables) = C.substTyVarBndrs (C.mkEmptySubst (C.substInScopeSet constructorRename)) measureVariables
        replacements substitution variables = [(rTyVar variable, ofType (C.substTy substitution (mkTyVarTy variable))) | variable <- variables]
        transport replacements' ty = L.foldl' (flip subsTyVarMeet') ty replacements'
        transportBody replacements' original = case original of
            E value -> E (expression value)
            P predicate -> P (expression predicate)
            R binder predicate -> R binder (expression predicate)
          where
            expression = subts [(variable, toRSort ty) | (variable, ty) <- replacements']
        measureReplacements = replacements measureRename measureVariables
        freshDefinition = (mapDefTy (transport measureReplacements) definition){body = transportBody measureReplacements body}
        freshInput = transport measureReplacements input
        freshArguments = C.substTys constructorRename arguments
        freshResult = C.substTy constructorRename result
    observed <- definitionObservations Nothing actual freshDefinition
    guard (length arguments == length actualArguments)
    let observations =
            zip freshArguments actualArguments
                ++ [(freshResult, actualResult), (toType False freshInput, actualResult)]
                ++ [(annotation, actualType) | (actualType, annotation) <- observed]
        flexible = C.mkVarSet (freshConstructorVariables ++ freshMeasureVariables)
        scope = C.mkInScopeSet (C.tyCoVarsOfTypes (concatMap (\(left, right) -> [left, right]) observations) `C.unionVarSet` flexible)
        match substitution (left, right) =
            C.tcMatchTyX_BM (C.matchBindTv flexible) substitution (sourceFamily left) (sourceFamily right)
    substitution <- foldM match (C.mkEmptySubst scope) observations
    guard (all (\variable -> C.isEmptyVarSet (C.tyCoVarsOfType (C.substTy substitution (mkTyVarTy variable)) `C.intersectVarSet` flexible)) (freshConstructorVariables ++ freshMeasureVariables))
    let selected = replacements substitution (freshConstructorVariables ++ freshMeasureVariables)
        selectedDefinition = mapDefTy (transport selected) freshDefinition
        selectedInput = transport selected freshInput
        selectedBody = transportBody selected (bodyOf freshDefinition)
        annotations = [ty | Just ty <- dsort selectedDefinition : map snd (binds selectedDefinition)]
        admissible ty = isBase ty && isBaseTy (toType False ty) && isTrivial (topRTypeBase ty)
    guard (all admissible (selectedInput : annotations))
    let refts = map rTypeReft (selectedInput : annotations)
        freePredicate (Reft (binder, predicate)) = F.syms predicate `S.difference` S.singleton binder
        bodyNames = case selectedBody of
            E value -> F.syms value
            P predicate -> F.syms predicate
            R binder predicate -> F.syms predicate `S.difference` S.singleton binder
        names = S.fromList (map fst fields) `S.union` S.unions (map freePredicate refts) `S.union` bodyNames
        originalBinder = maybe F.vv_ rTypeValueVar (dsort selectedDefinition)
        (_, receiverBinder) = F.freshInNS originalBinder names
        premise value ty = case rTypeReft ty of
            Reft (binder, predicate) -> subst1 predicate (binder, EVar value)
        conditions =
            premise receiverBinder selectedInput
                : maybe [] (\ty -> [premise receiverBinder ty]) (dsort selectedDefinition)
                ++ [premise field ty | (field, Just ty) <- binds selectedDefinition]
        receiver = mapRBase (const (Reft (receiverBinder, PTrue))) (ofType (sourceFamily actualResult))
    pure (refineWithCtorBody dc name (Just (Reft (receiverBinder, F.pAnd conditions))) selectedBody receiver)
  where
    template = Ghc.dataConWrapperType dc
    (constructorVariables, arguments, result) = splitType template
    (actualVariables, actualArguments, actualResult) = splitType actual
    declaration = toRTypeRep signature
    measureVariables = [variable | (binder, _) <- ty_vars declaration, let RTV variable = ty_var_value binder]
    bodyOf (Def _ _ _ _ originalBody) = originalBody

-- | If there are any dummy symbols in the type, replace them with fresh
-- variables.
--
-- WARNING: the current implementation might rename variables named as
-- dummySymbols event if they are not in the scope of the binder of a
-- dummy symbol. Might not be a problem at the places where noDummySyms is used,
-- but be careful if you want to use it in other places.
noDummySyms
  :: (OkRT c tv r, Subable r, Variable r ~ Symbol, IsReft r, ReftVar r ~ Symbol)
  => RType c tv r -> RType c tv r
noDummySyms t
  | any isDummy (ty_binds rep)
  = F.subst su t -- substitution forces renaming of ty_binds to fresh variables
  | otherwise
  = t
  where
    rep = toRTypeRep t
    su  = mkSubst [ (v, EVar v) | v <- ty_binds rep ]

combineDCTypes :: String -> Type -> [RRType Reft] -> RRType Reft
combineDCTypes _msg t ts = L.foldl' strengthenRefTypeGen (ofType t) ts

-- should constructors have implicits? probably not
defRefType :: Bool -> Maybe Reft -> Type -> Def (RRType Reft) DataCon -> RRType Reft
defRefType allowTC domain tdc definition@(Def f dc mt xs body) =
    generalize $ mkArrow as' [] xts t'
  where
    xts = stitchArgs allowTC (fSrcSpan f) dc xs ts
    t' = refineWithCtorBody dc f domain body t
    t = Mb.fromMaybe (ofType tr) mt
    (αs, arguments, result) = splitType tdc
    -- An observed equation and its omitted evidence must share one type
    -- instantiation. Mixing the worker's variables with the observation's
    -- variables invents extra quantifiers when the equation is generalized.
    substitution = Mb.fromMaybe mismatch (definitionMatch tdc definition)
    ts = C.substTys substitution arguments
    tr = C.substTy substitution result
    mismatch = panicDataCon (fSrcSpan f) dc (Text.PrettyPrint.HughesPJ.text "measure equation disagrees with constructor carriers")
    as = if Mb.isJust mt then [] else makeRTVar . rTyVar <$> αs
    as' = map (,mempty) as

splitType :: Type -> ([TyVar],[Type], Type)
splitType t  = (αs, map irrelevantMult ts, tr)
  where
    (αs, tb) = splitForAllTyCoVars t
    (ts, tr) = splitFunTys tb

stitchArgs :: Monoid t1
           => Bool
           -> SrcSpan
           -> DataCon
           -> [(Symbol, Maybe (RRType Reft))]
           -> [Type]
           -> [(Symbol, RFInfo, RRType Reft, t1)]
stitchArgs allowTC sp dc allXs allTs
  | nXs == nTs         = (g (dummySymbol, Nothing) . ofType <$> pts)
                      ++ zipWith g xs (ofType <$> ts)
  | otherwise          = panicFieldNumMismatch sp dc nXs nTs
    where
      (pts, ts)        = L.partition (\t -> notracepp ("isPredTy: " ++ showpp t) $ isErasable t) allTs
      (_  , xs)        = L.partition (coArg . snd) allXs
      nXs              = length xs
      nTs              = length ts
      g (x, Just t) _  = (x, classRFInfo allowTC, t, mempty)
      g (x, _)      t  = (x, classRFInfo allowTC, t, mempty)
      coArg Nothing    = False
      coArg (Just t)   = isErasable (toType False t)
      isErasable = isEmbeddedDictType

panicFieldNumMismatch :: (PPrint a, PPrint a1, PPrint a3)
                      => SrcSpan -> a3 -> a1 -> a -> a2
panicFieldNumMismatch sp dc nXs nTs  = panicDataCon sp dc msg
  where
    msg = "Requires" <+> pprint nTs <+> "fields but given" <+> pprint nXs

panicDataCon :: PPrint a1 => SrcSpan -> a1 -> Doc -> a
panicDataCon sp dc d
  = panicError $ ErrDataCon sp (pprint dc) d

refineWithCtorBody ::
    (Outputable a) =>
    a ->
    F.Located LHName ->
    Maybe Reft ->
    Body ->
    RType c tv Reft ->
    RType c tv Reft
refineWithCtorBody dc f domain body t =
    case stripRTypeBase t of
        Just (Reft (v, _)) ->
            strengthen t $
                Reft (v, guarded v)
        Nothing ->
            panic Nothing $ "measure mismatch " ++ showpp f ++ " on con " ++ showPpr dc
  where
    guarded receiver =
        let self = eApps (EVar $ lhNameToResolvedSymbol $ val f) [eVar receiver]
            condition = case domain of
                Nothing -> PTrue
                Just (Reft (value, predicate)) -> subst1 predicate (value, EVar receiver)
         in case condition of
                PTrue -> bodyPred self body
                _ -> case body of
                    E rhs -> bodyPred self (E (EIte condition rhs self))
                    P rhs -> bodyPred self (P (EIte condition rhs self))
                    R _ _ -> PImp condition (bodyPred self body)


bodyPred ::  Expr -> Body -> Expr
bodyPred fv (E e)    = PAtom Eq fv e
bodyPred fv (P p)    = PIff  fv p
bodyPred fv (R v' p) = subst1 p (v', fv)
