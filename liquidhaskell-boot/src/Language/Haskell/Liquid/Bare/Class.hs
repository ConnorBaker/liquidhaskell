{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp  #-}
{-# LANGUAGE TupleSections     #-}

{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Language.Haskell.Liquid.Bare.Class
  ( makeClasses
  , makeSpecDictionaries
  , makeDefaultMethods
  , makeMethodTypes
  , instanceDictionaryOwners
  , classMethodField
  , nominalEqualitySubstitution
  , dictionaryEqualitySubstitution
  )
  where

import GHC.Core.TyCon (isVisibleTyConBinder)
import qualified GHC.Core.Unify as Unify
import qualified GHC.Core.Type as GhcType
import qualified GHC.Types.Var as GhcVar
import           Data.Bifunctor
import qualified Data.Maybe                                 as Mb
import qualified Data.List                                  as L
import qualified Data.HashMap.Strict                        as M
import qualified Data.HashSet                               as S

import qualified Language.Fixpoint.Types                    as F
import qualified Language.Fixpoint.Types.Visitor            as F

import           Language.Haskell.Liquid.Types.Dictionaries
import qualified Language.Haskell.Liquid.GHC.Misc           as GM
import qualified Liquid.GHC.API            as Ghc
import qualified GHC.Core.Type            as Ghc (seqTypes)
import qualified GHC.Core.Predicate       as Ghc (getEqPredTys_maybe)
import qualified GHC.Core.Coercion.Axiom  as Ghc (Role(Nominal))
import qualified GHC.Core.Unify           as Ghc (tcUnifyTys, BindFlag(..))
import qualified GHC.Core.TyCo.Subst      as Ghc (substTy)
import qualified GHC.Builtin.Types        as Ghc (eqTyCon, heqTyCon)
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.Types.DataDecl
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.UX.Config (getConfig, typeclass)

import qualified Language.Haskell.Liquid.Measure            as Ms
import           Language.Haskell.Liquid.Bare.Types         as Bare
import           Language.Haskell.Liquid.Bare.Resolve       as Bare
import           Language.Haskell.Liquid.Bare.Expand        as Bare
import           Language.Haskell.Liquid.Bare.Misc         as Bare

import           Language.Haskell.Liquid.Bare.ToBare (specToBare)
import qualified GHC.Builtin.Names        as Names (eqClassName)
import qualified GHC.Core.Class           as Class (Class (..), classMethods)
import qualified GHC.Core.DataCon         as DataCon (dataConOrigArgTys, isVanillaDataCon)
import qualified GHC.Core.InstEnv         as InstEnv (ClsInst (..))
import qualified GHC.Core.TyCo.Rep        as Rep (mkVisFunTysMany, scaledThing)
import qualified GHC.Hs                   as Hs
import qualified GHC.Tc.Types             as Tc (TcGblEnv (..))
import           GHC.Types.Name.Reader (unLocWithUserRdr)
import           Text.PrettyPrint.HughesPJ (Doc, text)
import qualified Control.Exception                 as Ex
import Control.Monad (forM, guard)
import GHC.Core (InScopeEnv (ISE), Unfolding (NoUnfolding), mkVarApps)
import GHC.Core.Make (FloatBind (FloatLet))
import GHC.Core.Map.Expr (eqCoreExpr)
import GHC.Core.SimpleOpt (exprIsConApp_maybe)
import GHC.Types.Var.Env (mkInScopeSet)



-------------------------------------------------------------------------------
makeMethodTypes :: F.TCEmb Ghc.TyCon -> Bool -> DEnv Ghc.Var LocSpecType -> [(Ghc.Var, LocSpecType)] -> [DataConP] -> [Ghc.CoreBind] -> [(Ghc.Var, MethodType (F.Located CheckedSpecType))]
-------------------------------------------------------------------------------
makeMethodTypes embs allowTC (DEnv hm) dictionaryTypes cls cbs =
    [ ( method
      , MT
            (fmap logicalSpecType . addCC allowTC method . fromRISig <$> methodType dictionary selector)
            (Just $ fmap logicalSpecType $ addCC allowTC method $ classType dictionary selector)
            (Just (dictionary, selector))
      )
    | (dictionary, _) <- Ghc.flattenBinds cbs
    , Ghc.isDFunId dictionary
    , M.member dictionary hm || Mb.isJust (classDeclaration dictionary)
    , (selector, method) <- owners dictionary
    ]
        ++ [ ( selector
             , ImportedMethod
                (Just $ fmap logicalSpecType $ normalize $ fromRISig signature)
                (Just $ fmap logicalSpecType $ normalize $ classType dictionary selector)
                (Just (dictionary, selector))
             )
           | (dictionary, fields) <- M.toList hm
           , not (dictionary `S.member` localDictionaries)
           , let (_, _, owner, _) = Ghc.tcSplitDFunTy (Ghc.varType dictionary)
           , selector <- Ghc.classAllSelIds owner
           , Just signature <- [M.lookup (F.symbol (Ghc.getOccString selector)) fields]
           , let field = haskellClassField dictionary selector
                 representation = toRTypeRep (ofType $ Ghc.varType dictionary)
                 methodCarrier = toType False $ fromRTypeRep representation{ty_res = field}
                 normalize = addCCType allowTC selector methodCarrier
           ]
  where
    localDictionaries = S.fromList [dictionary | (dictionary, _) <- Ghc.flattenBinds cbs, Ghc.isDFunId dictionary]
    dictionaryTypeMap = M.fromList dictionaryTypes

    dictionaryArguments dictionary =
        map (specializeEquality dictionary) $ case M.lookup dictionary dictionaryTypeMap of
            Just signature | RApp _ arguments _ _ <- ty_res (toRTypeRep $ val signature) -> arguments
            _ -> map ofType $ fourth $ Ghc.tcSplitDFunTy (Ghc.varType dictionary)

    -- A GHC instance may expose a concrete head through equality evidence,
    -- e.g. forall a. a ~ Char => IsString [a]. Admission uses that evidence's
    -- specialization, while the callable dictionary keeps its actual telescope.
    specializeEquality dictionary argument =
        case dictionaryEqualitySubstitution dictionary of
            Just substitution -> foldl (flip (subsTyVarMeetWith embs)) argument [(rTyVar variable, ofType image) | (variable, image) <- substitution]
            Nothing -> Ex.throw (ErrOther location (text "Unsupported nominal equality specialization for instance dictionary") :: Error)
      where
        location = maybe (Ghc.getSrcSpan dictionary) GM.fSrcSpan (M.lookup dictionary dictionaryTypeMap)

    owners dictionary =
        Mb.fromMaybe
            ( panic
                (Just (Ghc.getSrcSpan dictionary))
                "Unsupported refined class dictionary: each field must retain its exact source owner and instance telescope"
            )
            (instanceDictionaryOwners cbs dictionary)

    classDeclaration dictionary =
        let (_, _, owner, _) = Ghc.tcSplitDFunTy (Ghc.varType dictionary)
         in L.find ((== Ghc.classDataCon owner) . dcpCon) cls

    classType dictionary selector =
        Mb.fromMaybe
            (F.loc (GM.locNamedThing selector) `F.atLoc` haskellClassField dictionary selector)
            declared
      where
        declared = do
            declaration <- classDeclaration dictionary
            field <-
                L.lookup
                    (Just (Ghc.getName selector))
                    [(getLHGHCName name, ty) | (name, ty) <- dcpTyArgs declaration]
            pure $ dcpLoc declaration `F.atLoc` subst (zip (dcpFreeTyVars declaration) (dictionaryArguments dictionary)) field

    haskellClassField dictionary selector =
        let (_, _, owner, _) = Ghc.tcSplitDFunTy (Ghc.varType dictionary)
         in subst
                (zip (map rTyVar $ Ghc.classTyVars owner) (dictionaryArguments dictionary))
                (ofType $ thrd3 $ Ghc.tcSplitMethodTy $ Ghc.varType selector)

    -- The dictionary already fixes the class owner. Its declaration selector,
    -- not the implementation's occurrence spelling, supplies the field key.
    methodType dictionary selector = do
        fields <- M.lookup dictionary hm
        M.lookup (F.symbol (Ghc.getOccString selector)) fields

    subst [] t = t
    subst ((a, ta) : su) t = subsTyVarMeetWith embs (a, ta) (subst su t)

    fourth (_, _, _, value) = value

-- Joint nominal evidence has one coordinated image, independent of clause
-- order. GHC's conservative family unification is not itself an equality proof:
-- require the image to discharge every pair and to be idempotent before using
-- the existing scoped refinement substitutions. Only the DFun's variables bind.
-- | The images that a DFun's nominal equality evidence fixes for its own type
--   variables, e.g. @a := Char@ for @forall a. a ~ Char => IsString [a]@.
dictionaryEqualitySubstitution :: Ghc.Var -> Maybe [(Ghc.TyVar, Ghc.Type)]
dictionaryEqualitySubstitution dictionary = nominalEqualitySubstitution variables equalities
  where
    (variables, context, _, _) = Ghc.tcSplitDFunTy (Ghc.varType dictionary)
    equalities = [pair | predicate <- context, Just pair <- [equality predicate]]
    equality predicate
        | Just (Ghc.Nominal, left, right) <- Ghc.getEqPredTys_maybe predicate = Just (left, right)
        | Just (constructor, arguments) <- Ghc.splitTyConApp_maybe predicate
        , constructor `elem` [Ghc.eqTyCon, Ghc.heqTyCon]
        , right : left : _ <- reverse arguments =
            Just (left, right)
        | otherwise = Nothing

nominalEqualitySubstitution :: [Ghc.TyVar] -> [(Ghc.Type, Ghc.Type)] -> Maybe [(Ghc.TyVar, Ghc.Type)]
nominalEqualitySubstitution variables equalities = do
    substitution <- Ghc.tcUnifyTys bind (map fst equalities) (map snd equalities)
    let images = [(variable, Ghc.substTy substitution (Ghc.TyVarTy variable)) | variable <- variables]
    guard (all (\(left, right) -> Ghc.substTy substitution left `Ghc.eqType` Ghc.substTy substitution right) equalities)
    guard (all (\(_, image) -> Ghc.substTy substitution image `Ghc.eqType` image) images)
    pure [(variable, image) | (variable, image) <- images, not (Ghc.TyVarTy variable `Ghc.eqType` image)]
  where
    bind variable _
        | variable `elem` variables = Ghc.BindMe
        | otherwise = Ghc.DontBindMe

addCC :: Bool -> Ghc.Var -> LocSpecType -> LocSpecType
addCC allowTC var = addCCType allowTC var (Ghc.varType var)

addCCType :: Bool -> Ghc.Var -> Ghc.Type -> LocSpecType -> LocSpecType
addCCType allowTC var t0 zz@(Loc l l' st0)
    | length sourceClasses <= length haskellClasses
    , toType False hst `Ghc.eqType` toType False result =
        Loc l l' result
    | otherwise = Ex.throw (err (pprint hst) (pprint result))
  where
    result = addForall [] hst (mkArrow [] [] contextClasses (tx (stripPrefixForalls st0)))
    hst = ofType (Ghc.expandTypeSynonyms t0) :: SpecType
    tyvsmap = case Bare.runMapTyVars
        allowTC
        (toType False (mkArrow [] [] (rows matchingClasses) rt))
        (mkArrow [] [] (rows sourceClasses) st)
        err of
        Left e -> Ex.throw e
        Right s -> Bare.vmap s
    su = [(y, rTyVar x) | (x, y) <- tyvsmap]
    su' = [(source, RVar target NoReft) | (source, target) <- su] :: [(RTyVar, RSort)]
    -- The absent prefix belongs to the instance context; the supplied suffix
    -- owns its dictionary labels and every dependent use in the method body.
    (context, matchingClasses) = splitAt (length haskellClasses - length sourceClasses) haskellClasses
    contextClasses = rows context
    rows = map (\(x, t, r) -> (x, classRFInfo allowTC, t, r))
    tx = subts su'
    (_, _, haskellClasses, rt) = classTelescope hst
    (sourceVariables, _, sourceClasses, st) = classTelescope st0

    -- Flatten only for type-variable alignment, never for reconstruction:
    -- instance evidence may precede a method's forall and abstract predicates.
    classTelescope :: SpecType -> ([(SpecRTVar, RReft)], [PVar RSort], [(F.Symbol, SpecType, RReft)], SpecType)
    classTelescope ty =
        let (as, ps0, cs, body) = bkUnivClass' ty
            continue =
                let (as', ps'', cs', result) = classTelescope body
                 in (as ++ as', ps0 ++ ps'', cs ++ cs', result)
         in case body of
                RAllT{} -> continue
                RAllP{} -> continue
                _ -> (as, ps0, cs, body)

    -- Retain predicate and dictionary binders in place, including their named
    -- dependent uses. The GHC telescope supplies the type binders again below.
    stripPrefixForalls :: SpecType -> SpecType
    stripPrefixForalls (RAllT _ t _) = stripPrefixForalls t
    stripPrefixForalls (RAllP p t) = RAllP p (stripPrefixForalls t)
    stripPrefixForalls (RFun x i t@(RApp c _ _ _) t' r)
        | isClass c = RFun x i t (stripPrefixForalls t') r
    stripPrefixForalls t = t

    err :: Doc -> Doc -> Error
    err hsT lqT =
        ErrMismatch
            (GM.fSrcSpan zz)
            (pprint var)
            (text "makeMethodTypes")
            (pprint $ Ghc.expandTypeSynonyms t0)
            (pprint $ toRSort st0)
            (Just (hsT, lqT))
            (Ghc.getSrcSpan var)

    addForall :: [RTyVar] -> SpecType -> SpecType -> SpecType
    addForall scope (RAllT v t r) tt@(RAllT v' _ _)
        | v == v' =
            tt
        | otherwise =
            RAllT (updateRTVar v) (addForall (ty_var_value v : scope) t tt) r
    addForall scope (RAllT v t r) t' =
        RAllT (updateRTVar v) (addForall (ty_var_value v : scope) t t') (r <> sourceReft v)
    addForall scope (RAllP _ t) t' =
        addForall scope t t'
    addForall scope t (RAllP p t')
        | all ((`elem` scope) . ty_var_value) (concatMap freeTyVars (ptype p : [s | (s, _, _) <- pargs p])) =
            RAllP p (addForall scope t t')
        | otherwise =
            Ex.throw (err (pprint t) (text "Abstract predicate is outside the scope of its method type variables:" <> pprint p))
    addForall scope (RFun _ _ t1 t2 _) (RFun x i t1' t2' r) =
        RFun x i (addForall scope t1 t1') (addForall scope t2 t2') r
    addForall _ _ t =
        t

    sourceReft :: SpecRTVar -> RReft
    sourceReft v =
        mconcat
            [ subts su' r
            | (a, r) <- sourceVariables
            , Mb.fromMaybe (ty_var_value a) (lookup (ty_var_value a) su) == ty_var_value v
            ]

-- A selector owns its actual dictionary field, not a spelling such as $cp1.
-- Follow only local administrative aliases; a top-level method remains its
-- own proof root. GHC owns constructor recognition and the complete telescope.
instanceDictionaryOwners :: Ghc.CoreProgram -> Ghc.Var -> Maybe [(Ghc.Var, Ghc.Var)]
instanceDictionaryOwners program dictionaryOwner = do
  guard (Ghc.isDFunId dictionaryOwner)
  rhs <- lookup dictionaryOwner definitions
  let (parameters, body) = Ghc.collectBinders rhs
  (sourceAliases, dictionary) <- dictionaryBody [] [] body
  let scope = ISE (mkInScopeSet (Ghc.exprFreeVars dictionary)) (const NoUnfolding)
  (_, floats, constructor, _, fields) <- exprIsConApp_maybe scope dictionary
  guard (constructor == Ghc.classDataCon cls)
  guard (length fields == length selectors)
  floatedAliases <- traverse nonRecursiveAlias floats
  owners <- traverse (sourceOwner parameters (floatedAliases ++ sourceAliases) []) fields
  -- One declaration shared by different fields would require meeting all
  -- their contracts; never silently overwrite one field's obligation.
  guard (length (L.nub owners) == length owners)
  pure (zip selectors owners)
  where
    (_, _, cls, _) = Ghc.tcSplitDFunTy (Ghc.varType dictionaryOwner)
    selectors = Ghc.classAllSelIds cls
    definitions = Ghc.flattenBinds program
    dictionaryBody aliases visited expression = case expression of
      Ghc.Let (Ghc.NonRec owner rhs) body -> dictionaryBody ((owner, rhs) : aliases) visited body
      Ghc.Var owner
        | owner `elem` visited -> Nothing
        | Just rhs <- lookup owner aliases -> dictionaryBody aliases (owner : visited) rhs
      _ -> Just (aliases, expression)
    nonRecursiveAlias (FloatLet (Ghc.NonRec owner rhs)) = Just (owner, rhs)
    nonRecursiveAlias _ = Nothing
    sourceOwner parameters aliases visited field = case Ghc.collectArgs field of
      (Ghc.Var owner, arguments)
        | owner `elem` visited -> Nothing
        | Just rhs <- lookup owner aliases -> sourceOwner parameters aliases (owner : visited) (Ghc.mkApps rhs arguments)
        | Just _ <- lookup owner definitions
        , field `eqCoreExpr` mkVarApps (Ghc.Var owner) parameters
        , Ghc.varType owner `Ghc.eqType` Ghc.exprType (Ghc.mkLams parameters field) ->
            Just owner
      _ -> Nothing


-------------------------------------------------------------------------------
makeClasses :: Bare.Env -> Bare.SigEnv -> ModName -> Bare.ModSpecs
            -> Bare.Lookup ([DataConP], [(ModName, Ghc.Var, LocSpecType)])
-------------------------------------------------------------------------------
makeClasses env sigEnv myName specs = do
  mbZs <- forM classTcs $ \(name, cls, tc) ->
            mkClass env sigEnv myName name cls tc
  return . second mconcat . unzip . Mb.catMaybes $ mbZs
  where
    classTcs = [ (name, cls, tc) | (name, spec) <- M.toList specs
                                 , cls          <- Ms.classes spec
                                 , tc           <- Mb.maybeToList (classTc cls) ]
    classTc = either (const Nothing) Just . Bare.lookupGhcTyConLHName (reTyLookupEnv env) . btc_tc . rcName

mkClass :: Bare.Env -> Bare.SigEnv -> ModName -> ModName -> RClass LocBareType -> Ghc.TyCon
        -> Bare.Lookup (Maybe (DataConP, [(ModName, Ghc.Var, LocSpecType)]))
mkClass env sigEnv _myName name (RClass cc ss as ms)
  = Bare.failMaybe env name
  . mkClassE env sigEnv _myName name (RClass cc ss as ms)

mkClassE :: Bare.Env -> Bare.SigEnv -> ModName -> ModName -> RClass LocBareType -> Ghc.TyCon
         -> Bare.Lookup (DataConP, [(ModName, Ghc.Var, LocSpecType)])
mkClassE env sigEnv _myName name (RClass cc ss as ms) tc = do
    ss'    <- mapM (mkConstr   env sigEnv name) ss
    meths  <- mapM (makeMethod env sigEnv name) ms'
    let vts = [ (m, v, t) | (m, kv, t) <- meths, v <- Mb.maybeToList (plugSrc kv) ]
    let sts = [(val s, classMethodField tc (implicit ++ αs) t) | (s, _) <- ms | (_, _, t) <- meths]
    let dcp = DataConP l dc (implicit ++ αs) [] (val <$> ss') (reverse sts) rt False (F.symbol name) l'
    return  $ F.notracepp msg (dcp, vts)
  where
    c = btc_tc cc
    l = loc c
    l' = locE c
    msg = "MKCLASS: " ++ F.showpp (cc, as, αs)
    (dc : _) = Ghc.tyConDataCons tc
    αs = bareRTyVar <$> as
    as' = [rVar $ GM.symbolTyVar $ F.symbol a | a <- as]
    ms' = [(s, rFun "" (RApp cc (flip RVar mempty <$> as) [] mempty) <$> t) | (s, t) <- ms]
    -- The authored head names only visible parameters. GHC's dictionary
    -- constructor also binds the class's implicit (e.g. generalized kind)
    -- parameters; they are owned by the constructor, not by any method.
    implicitVars = [Ghc.binderVar b | b <- Ghc.tyConBinders tc, not (isVisibleTyConBinder b)]
    implicit = rTyVar <$> implicitVars
    rt = rApp tc ((rVar <$> implicitVars) ++ as') [] trueReft

mkConstr :: Bare.Env -> Bare.SigEnv -> ModName -> LocBareType -> Bare.Lookup LocSpecType
mkConstr env sigEnv name = fmap (fmap dropUniv) . Bare.cookSpecTypeE env sigEnv name Bare.GenTV

-- A selector fixes only its class owner. Method-local quantifiers and runtime
-- evidence remain part of the dictionary field, even when GHC hoists those
-- quantifiers before the owner dictionary in the selector telescope.
classMethodField :: Ghc.TyCon -> [RTyVar] -> LocSpecType -> SpecType
classMethodField owner variables located = case body of
    RFun ownerName _ dictionary@(RApp constructor arguments _ _) field arrowReft
        | rtc_tc constructor == owner
        , Just selected <- traverse variable arguments
        , length selected == length variables
        , length (L.nub selected) == length selected
        , all (`elem` map (ty_var_value . fst) binders) selected
        , all isTauto [reft | (binder, reft) <- binders, ty_var_value binder `elem` selected]
        , all isTauto dictionary
        , isTauto arrowReft
        , let retained = mkUnivs [(binder, reft) | (binder, reft) <- binders, ty_var_value binder `notElem` selected] predicates field
        , not (ownerName `S.member` F.syms retained) ->
            subts (zip selected [RVar variable NoReft :: RSort | variable <- variables]) retained
    _ -> Ex.throw (ErrOther (GM.fSrcSpan located) (text "Class method selector does not preserve its owner and local telescope") :: Error)
  where
    (binders, predicates, body) = bkUniv (val located)
    variable (RVar v _) = Just v
    variable _ = Nothing

makeMethod :: Bare.Env -> Bare.SigEnv -> ModName -> (Located LHName, LocBareType)
           -> Bare.Lookup (ModName, PlugTV Ghc.Var, LocSpecType)
makeMethod env sigEnv name (lx, bt) = (name, mbV,) <$> Bare.cookSpecTypeE env sigEnv name mbV bt
  where
    mbV = either (const Bare.GenTV) Bare.LqTV (Bare.lookupGhcIdLHName env lx)

-------------------------------------------------------------------------------
makeSpecDictionaries ::
    Tc.TcGblEnv ->
    Bare.Env ->
    Bare.SigEnv ->
    (ModName, Ms.BareSpec) ->
    [(ModName, Ms.BareSpec)] ->
    Ghc.TcRn ([RInstance LocBareType], DEnv Ghc.Var LocSpecType, DEnv Ghc.Var LocSpecType, [(Ghc.Var, LocSpecType)])
-------------------------------------------------------------------------------
-- The module's own instance declarations, then those it may use: its own and
-- imported ones. An imported declaration is a premise its owner established
-- (or, under --compile-spec, trusted); only the declaring module checks it.
makeSpecDictionaries tcg env sigEnv spec0 specs =
    do
        (instances, specDicts, dictionaryTypes) <- makeSpecDictionary env sigEnv spec0
        imported <- mapM (makeSpecDictionary env sigEnv) specs
        instEnvs <- Ghc.tcGetInstEnvs
        -- Assumed, so not among the declared (checked) dictionaries.
        let derived = derivedEqualityInstances tcg instEnvs (dfromList $ specDicts ++ concatMap (\(_, dictionaries, _) -> dictionaries) imported)
        derivedDicts <- resolveDictionaries env (map (makeSpecDictionaryOne env sigEnv (fst spec0)) derived)
        let allDictionaryTypes = dictionaryTypes ++ concatMap (\(_, _, signatures) -> signatures) imported
            declarations = M.fromListWith (flip (++)) [(dictionary, [GM.fSrcSpan signature]) | (dictionary, signature) <- allDictionaryTypes]
            duplicates = [errDupSpecs (pprint dictionary) locations :: Error | (dictionary, locations@(_ : _ : _)) <- M.toList declarations]
        case duplicates of
            err : _ -> Ghc.liftIO $ Ex.throwIO err
            [] -> pure ()
        pure
            ( instances ++ derived
            , dfromList specDicts
            , dfromList $ specDicts ++ derivedDicts ++ concatMap (\(_, dictionaries, _) -> dictionaries) imported
            , allDictionaryTypes
            )

-- | Stock-derived equality. Haskell 2010 Report, chapter 11 (Specification
-- of Derived Instances), section 11.1: a derived (==) holds exactly when both
-- values have the same constructor and their corresponding fields are (==).
-- GHC 9.14.1 generates only (==) for stock Eq (GHC/Tc/Deriv/Generate.hs:
-- 218-261), and for a data declaration a deriving clause without a strategy
-- derives a stock class by stock deriving (GHC/Tc/Deriv.hs:1524-1576,
-- GHC/Tc/Deriv/Utils.hs:857-881).
--
-- When every field's (==) is the logical equality of its values, the derived
-- (==) is therefore the logical equality of the datatype's values. This
-- module's monomorphic data types whose own deriving clause derives Eq by the
-- stock strategy, and whose constructors are vanilla, receive that contract as
-- an assumed instance method, published to importers. A field type qualifies
-- when its Eq instance contract is exactly @x:t -> y:t -> {v | v <=> x = y}@
-- or it is such a derived type of this module; the least fixed point leaves
-- recursive types out. An authored instance specification takes precedence.
-- No other instance, e.g. one derived via another type, a newtype, a type
-- with a parameter, or one whose field's (==) is not logical equality (such
-- as Text's, which compares content while its logical values are
-- representations), receives a contract.
derivedEqualityInstances :: Tc.TcGblEnv -> Ghc.InstEnvs -> DEnv Ghc.Var LocSpecType -> [RInstance LocBareType]
derivedEqualityInstances tcg instEnvs (DEnv known) = map instanceOf (accept [])
  where
    candidates =
        [ (InstEnv.is_cls inst, ty, tc, InstEnv.is_dfun inst)
        | inst <- Tc.tcg_insts tcg
        , Class.className (InstEnv.is_cls inst) == Names.eqClassName
        , null (InstEnv.is_tvs inst)
        , [ty] <- [InstEnv.is_tys inst]
        , Just (tc, []) <- [Ghc.splitTyConApp_maybe ty]
        , Ghc.getName tc `elem` stockEqualities
        , not (M.member (InstEnv.is_dfun inst) known)
        , all DataCon.isVanillaDataCon (Ghc.tyConDataCons tc)
        ]
    accept accepted = case [candidate | candidate@(cls, _, tc, _) <- candidates, tc `notElem` accepted, all (qualifies cls accepted) (fields tc)] of
        [] -> [candidate | candidate@(_, _, tc, _) <- candidates, tc `elem` accepted]
        new -> accept (accepted ++ [tc | (_, _, tc, _) <- new])
    fields tc = [Rep.scaledThing field | constructor <- Ghc.tyConDataCons tc, field <- DataCon.dataConOrigArgTys constructor]
    qualifies cls accepted ty = case Ghc.splitTyConApp_maybe ty of
        Just (tc, []) | tc `elem` accepted -> True
        _ -> case Ghc.lookupInstEnv False instEnvs cls [ty] of
            ([(inst, _)], _, _)
                | Just methods <- M.lookup (Ghc.is_dfun inst) known
                , Just signature <- M.lookup equalitySymbol methods ->
                    meansEquality (val (fromRISig signature))
            _ -> False
    instanceOf (cls, ty, _, dfun) =
        RI
            { riclass = tyConBTyCon (Class.classTyCon cls)
            , riDictName = Just (makeGHCLHNameLocatedFromId dfun)
            , ritype = [located (specToBare (ofType ty :: SpecType))]
            , risigs =
                -- Instance method keys are the method's occurrence name.
                [ (located (makeGHCLHName (Ghc.getName selector) equalitySymbol), RIAssumed (located (specToBare (equalityContract ty))))
                | selector <- Class.classMethods cls
                , F.symbol (Ghc.getOccString selector) == equalitySymbol
                ]
            }
      where
        located = F.atLoc (GM.locNamedThing dfun)
    stockEqualities =
        [ Ghc.unLoc (Hs.tcdLName declaration)
        | Just group <- [Tc.tcg_rn_decls tcg]
        , Ghc.L _ declaration@Hs.DataDecl{Hs.tcdDataDefn = Hs.HsDataDefn{Hs.dd_cons = Hs.DataTypeCons False _, Hs.dd_derivs = clauses}} <- Hs.tyClGroupTyClDecls (Hs.hs_tyclds group)
        , Ghc.L _ clause <- clauses
        , maybe True (stock . Ghc.unLoc) (Hs.deriv_clause_strategy clause)
        , Ghc.L _ Hs.HsSig{Hs.sig_body = body} <- derivedClasses (Ghc.unLoc (Hs.deriv_clause_tys clause))
        , Just name <- [Hs.hsTyGetAppHead_maybe body]
        , unLocWithUserRdr name == Names.eqClassName
        ]
    stock Hs.StockStrategy{} = True
    stock _ = False
    derivedClasses (Hs.DctSingle _ ty) = [ty]
    derivedClasses (Hs.DctMulti _ tys) = tys

equalitySymbol :: F.Symbol
equalitySymbol = "=="

equalityContract :: Ghc.Type -> SpecType
equalityContract ty =
    fromRTypeRep
        representation
            { ty_binds = [x, y]
            , ty_res = strengthen (ty_res representation) (ofReft (F.Reft (F.vv_, F.PIff (F.EVar F.vv_) (F.PAtom F.Eq (F.EVar x) (F.EVar y)))))
            }
  where
    representation = toRTypeRep (ofType (Rep.mkVisFunTysMany [ty, ty] Ghc.boolTy) :: SpecType)
    x = "x"
    y = "y"

-- | The contract @x:t -> y:t -> {v:Bool | v <=> x = y}@, up to binder names
-- and the orientation of each connective.
meansEquality :: SpecType -> Bool
meansEquality ty = case (ty_binds representation, ty_args representation, rTypeReft (ty_res representation)) of
    ([x, y], [left, right], F.Reft (v, predicate)) ->
        null (ty_vars representation)
            && null (ty_preds representation)
            && all isTauto left
            && all isTauto right
            && F.conjuncts predicate `elem` [[F.PIff a b] | equal <- equalities x y, (a, b) <- [(F.EVar v, equal), (equal, F.EVar v)]]
    _ -> False
  where
    representation = toRTypeRep ty
    equalities x y = [F.PAtom relation a b | relation <- [F.Eq, F.Ueq], (a, b) <- [(F.EVar x, F.EVar y), (F.EVar y, F.EVar x)]]

makeSpecDictionary ::
    Bare.Env ->
    Bare.SigEnv ->
    (ModName, Ms.BareSpec) ->
    Ghc.TcRn ([RInstance LocBareType], [(Ghc.Var, M.HashMap F.Symbol (RISig LocSpecType))], [(Ghc.Var, LocSpecType)])
makeSpecDictionary env sigEnv (name, spec) = do
    let instances = Ms.rinstance spec
    let cooked = map (makeSpecDictionaryOne env sigEnv name) instances
    resolved <- resolveDictionaries env cooked
    let updatedInstances =
            [ ri{riDictName = Just $ makeGHCLHNameLocatedFromId v}
            | (ri, (v, _)) <- zip instances resolved
            ]
        dictionaryTypes =
            [ (dictionary, addCC (typeclass $ getConfig env) dictionary $ location `F.atLoc` headType)
            | (ri, (dictionary, _)) <- zip cooked resolved
            , let representation = toRTypeRep (ofType $ Ghc.varType dictionary)
                  arguments = map (dropUniv . val) (ritype ri)
                  headType = case ty_res representation of
                    actual@RApp{} | all (all isTauto) arguments -> actual
                    RApp constructor _ predicates refinement -> RApp constructor arguments predicates refinement
                    _ -> panic (Just $ Ghc.getSrcSpan dictionary) "Instance dictionary has no class result"
                  location = case ritype ri of
                    first : _ -> F.loc first
                    [] -> F.loc $ GM.locNamedThing dictionary
            ]
    pure (updatedInstances, resolved, dictionaryTypes)

makeSpecDictionaryOne :: Bare.Env -> Bare.SigEnv -> ModName
                      -> RInstance LocBareType
                      -> RInstance LocSpecType
makeSpecDictionaryOne env sigEnv name (RI bt mDictName lbt xts)
         = F.notracepp "RI" $ RI bt mDictName ts [(x, mkLSpecIType t) | (x, t) <- xts ]
  where
    ts      = mkTy' <$> lbt
    rts     = concatMap (univs . val) ts
    univs t = (\(RTVar tv _, _) -> tv) <$> as where (as, _, _) = bkUniv t

    mkTy' :: LocBareType -> LocSpecType
    mkTy' = Bare.cookSpecType env sigEnv name Bare.GenTV
    mkTy :: LocBareType -> LocSpecType
    mkTy = fmap (mapUnis tidy) . Bare.cookSpecType env sigEnv name
               Bare.GenTV -- (Bare.HsTV (Bare.lookupGhcVar env name "rawDictionaries" x))
    mapUnis f t = mkUnivs (f as) ps t0 where (as, ps, t0) = bkUniv t

    tidy vs = l ++ r
      where (l,r) = L.partition (\(RTVar tv _,_) -> tv `elem` rts) vs

    mkLSpecIType :: RISig LocBareType -> RISig LocSpecType
    mkLSpecIType t = fmap mkTy t

resolveDictionaries :: Bare.Env -> [RInstance LocSpecType]
                    -> Ghc.TcRn [(Ghc.Var, M.HashMap F.Symbol (RISig LocSpecType))]
resolveDictionaries env = mapM $ \ri -> do
    v <- lookupDFun ri
    pure (v, M.fromList $ first (getLHNameSymbol . val) <$> risigs ri)
  where
    lookupDFun (RI c (Just ldict) _ _) = do
       case Bare.lookupGhcIdLHName env ldict of
         Left e ->
           panic (Just $ GM.fSrcSpan $ btc_tc c) $
             "cannot find dictionary from name: " ++ show e
         Right v -> pure v
    lookupDFun (RI c _ ts _) = do
       let tys = map (toType False . dropUniv . val) ts
       case Bare.lookupGhcTyConLHName (reTyLookupEnv env) (btc_tc c) of
         Left _ ->
           panic (Just $ GM.fSrcSpan $ btc_tc c) "cannot find type class"
         Right tc -> case Ghc.tyConClass_maybe tc of
           Nothing ->
             panic (Just $ GM.fSrcSpan $ btc_tc c) "type constructor does not refer to a type class"
           Just cls -> do
             -- Resolving an LH-only head may load its owner's non-orphan
             -- instances. Read the instance environment after forcing it.
             Ghc.liftIO $ Ex.evaluate (Ghc.seqTypes tys)
             instEnvs <- Ghc.tcGetInstEnvs
             case Ghc.lookupInstEnv False instEnvs cls (classArguments tc tys) of
               -- Is it ok to pick the first match?
               ((clsInst, _) : _, _, _) ->
                 pure $ Ghc.is_dfun clsInst
               ([], _, _) ->
                 panic (Just $ GM.fSrcSpan $ btc_tc c) "cannot find class instance"

-- | An authored instance head names only the visible class arguments. The
-- implicit (e.g. generalized kind) arguments are determined by their kinds.
classArguments :: Ghc.TyCon -> [Ghc.Type] -> [Ghc.Type]
classArguments tc tys =
    case Unify.tcMatchTys (map GhcVar.varType visible) (map GhcType.typeKind tys) of
        Just su | length visible == length tys -> go su (Ghc.tyConBinders tc) tys
        _ -> tys
  where
    visible = [Ghc.binderVar b | b <- Ghc.tyConBinders tc, isVisibleTyConBinder b]
    go su (b : bs) args
        | isVisibleTyConBinder b, a : rest <- args = a : go su bs rest
        | otherwise = GhcType.substTyVar su (Ghc.binderVar b) : go su bs args
    go _ [] args = args

dropUniv :: SpecType -> SpecType
dropUniv t = t' where (_,_,t') = bkUniv t


----------------------------------------------------------------------------------
makeDefaultMethods :: Bare.Env -> [(ModName, Ghc.Var, LocSpecType)]
                   -> [(ModName, Ghc.Var, LocSpecType)]
----------------------------------------------------------------------------------
makeDefaultMethods env mts = [ (mname, dm, t)
                                 | (mname, m, t) <- mts
                                 , Just dm <- [lookupDefaultVar env m]
                             ]

lookupDefaultVar :: Bare.Env -> Ghc.Var -> Maybe Ghc.Var
lookupDefaultVar env v =
    case Ghc.idDetails v of
      Ghc.ClassOpId cls _ -> do
        mdm <- lookup v (Ghc.classOpItems cls)
        (n, dmspec) <- mdm
        case dmspec of
          Ghc.VanillaDM -> case lookupGhcIdLHName env (makeGHCLHNameLocated n) of
            Right x -> Just x
            _ -> Nothing
          _ -> Nothing
      _ -> Nothing
