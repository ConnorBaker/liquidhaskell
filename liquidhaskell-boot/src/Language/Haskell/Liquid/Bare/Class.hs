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
  )
  where

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
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.Types.DataDecl
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.Types

import qualified Language.Haskell.Liquid.Measure            as Ms
import           Language.Haskell.Liquid.Bare.Types         as Bare
import           Language.Haskell.Liquid.Bare.Resolve       as Bare
import           Language.Haskell.Liquid.Bare.Expand        as Bare
import           Language.Haskell.Liquid.Bare.Misc         as Bare

import           Text.PrettyPrint.HughesPJ (Doc, text)
import qualified Control.Exception                 as Ex
import Control.Monad (forM, guard)
import GHC.Core (InScopeEnv (ISE), Unfolding (NoUnfolding), mkVarApps)
import GHC.Core.Make (FloatBind (FloatLet))
import GHC.Core.Map.Expr (eqCoreExpr)
import GHC.Core.SimpleOpt (exprIsConApp_maybe)
import GHC.Types.Var.Env (mkInScopeSet)



-------------------------------------------------------------------------------
makeMethodTypes :: F.TCEmb Ghc.TyCon -> Bool -> DEnv Ghc.Var LocSpecType -> [DataConP] -> [Ghc.CoreBind] -> [(Ghc.Var, MethodType LocSpecType)]
-------------------------------------------------------------------------------
makeMethodTypes embs allowTC (DEnv hm) cls cbs =
  [ ( method
    , MT
        (addCC allowTC method . fromRISig <$> methodType dictionary selector)
        (addCC allowTC method <$> classType dictionary selector)
    )
  | (dictionary, _) <- Ghc.flattenBinds cbs
  , Ghc.isDFunId dictionary
  , M.member dictionary hm || Mb.isJust (classDeclaration dictionary)
  , (selector, method) <- owners dictionary
  ]
  where
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

    classType dictionary selector = do
      declaration <- classDeclaration dictionary
      field <-
        L.lookup
          (Just (Ghc.getName selector))
          [(getLHGHCName name, ty) | (name, ty) <- dcpTyArgs declaration]
      let (_, _, _, arguments) = Ghc.tcSplitDFunTy (Ghc.varType dictionary)
      pure $ dcpLoc declaration `F.atLoc` subst (zip (dcpFreeTyVars declaration) arguments) field

    -- The dictionary already fixes the class owner. Its declaration selector,
    -- not the implementation's occurrence spelling, supplies the field key.
    methodType dictionary selector = do
      fields <- M.lookup dictionary hm
      M.lookup (F.symbol (Ghc.getOccString selector)) fields

    subst [] t = t
    subst ((a, ta) : su) t = subsTyVarMeetWith embs (a, ofType ta) (subst su t)

addCC :: Bool -> Ghc.Var -> LocSpecType -> LocSpecType
addCC allowTC var zz@(Loc l l' st0)
  | length sourceClasses <= length haskellClasses
  , toType False hst `Ghc.eqType` toType False result =
      Loc l l' result
  | otherwise = Ex.throw (err (pprint hst) (pprint result))
  where
    result = addForall [] hst (mkArrow [] [] contextClasses (tx (stripPrefixForalls st0)))
    hst = ofType (Ghc.expandTypeSynonyms t0) :: SpecType
    t0 = Ghc.varType var
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
    let sts = [(val s, classMethodField tc αs t) | (s, _) <- ms | (_, _, t) <- meths]
    let dcp = DataConP l dc αs [] (val <$> ss') (reverse sts) rt False (F.symbol name) l'
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
    rt = rApp tc as' [] trueReft

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
makeSpecDictionaries
  :: Bare.Env
  -> Bare.SigEnv
  -> (ModName, Ms.BareSpec)
  -> [(ModName, Ms.BareSpec)]
  -> Ghc.TcRn ([RInstance LocBareType], DEnv Ghc.Var LocSpecType)
-------------------------------------------------------------------------------
makeSpecDictionaries env sigEnv spec0 specs
  = do (instances, specDicts) <- makeSpecDictionary env sigEnv spec0
       imported <- mapM (makeSpecDictionary env sigEnv) specs
       pure (instances, dfromList $ specDicts ++ concatMap snd imported)

makeSpecDictionary :: Bare.Env -> Bare.SigEnv -> (ModName, Ms.BareSpec)
                   -> Ghc.TcRn ([RInstance LocBareType], [(Ghc.Var, M.HashMap F.Symbol (RISig LocSpecType))])
makeSpecDictionary env sigEnv (name, spec) = do
    let instances = Ms.rinstance spec
    resolved <- resolveDictionaries env $ map (makeSpecDictionaryOne env sigEnv name) instances
    let updatedInstances =
          [ ri { riDictName = Just $ makeGHCLHNameLocatedFromId v }
          | (ri, (v, _)) <- zip instances resolved
          ]
    pure (updatedInstances, resolved)

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
             case Ghc.lookupInstEnv False instEnvs cls tys of
               -- Is it ok to pick the first match?
               ((clsInst, _) : _, _, _) ->
                 pure $ Ghc.is_dfun clsInst
               ([], _, _) ->
                 panic (Just $ GM.fSrcSpan $ btc_tc c) "cannot find class instance"

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
