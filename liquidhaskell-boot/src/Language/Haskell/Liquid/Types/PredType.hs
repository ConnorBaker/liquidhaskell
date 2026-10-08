{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Language.Haskell.Liquid.Types.PredType (
    TyConP (..), DataConP (..)
  , dataConTy
  , dataConPSpecType
  , dataConRuntimeFields
  , makeTyConInfo
  , replacePreds
  , replacePredsWithRefs
  , pVartoRConc

  -- * Dummy `Type` that represents _all_ abstract-predicates
  , predType

  -- * Compute @RType@ of a given @PVar@
  , pvarRType
  , substParg
  , pApp
  , pappSort
  , pappArity

  -- * should be elsewhere
  , dataConWorkRep
  , substPVar
  ) where

import           Prelude                         hiding (error)
import qualified Control.Exception as Ex
import qualified Text.PrettyPrint.HughesPJ as Pretty
import           Liquid.GHC.API hiding ( panic
                                                        , (<+>)
                                                        , hsep
                                                        , punctuate
                                                        , comma
                                                        , parens
                                                        , showPpr
                                                        )
import           Language.Haskell.Liquid.GHC.TypeRep ()
import qualified Data.HashMap.Strict             as M
import qualified Data.HashSet                    as S
import qualified Data.Maybe                                 as Mb
import qualified Data.List         as L -- (foldl', partition)
-- import           Data.List                       (nub)

import           Language.Fixpoint.Misc

-- import           Language.Fixpoint.Types         hiding (Expr, Predicate)
import qualified Language.Fixpoint.Types                    as F
import qualified Liquid.GHC.API            as Ghc
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.Types.DataDecl
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.RefType hiding (generalize)
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Variance
import qualified Language.Haskell.Liquid.Measure as Measure

makeTyConInfo :: F.TCEmb Ghc.TyCon -> [Ghc.TyCon] -> [Ghc.TyCon] -> [TyConP] -> TyConMap
makeTyConInfo tce fiTcs localTyCons tcps =
  TyConMap
    { tcmTyRTy = tcM
    , tcmFIRTy = tcInstM
    , tcmFtcArity = arities
    }
  where
    declarations = M.fromList [(tcpCon tcp, tcp) | tcp <- tcps]
    local = S.fromList localTyCons
    authored = M.mapMaybe (\tcp -> if null (tcpVarianceTs tcp) then Nothing else Just (map restriction (tcpVarianceTs tcp))) declarations
    lowerBounds = M.filterWithKey (\c _ -> S.member c local) authored
    external = M.difference authored lowerBounds
    variances = makeTyConVariances external lowerBounds (localTyCons ++ M.keys declarations)
    defaults = M.mapWithKey (\c vs -> RTyCon c [] (TyConInfo vs [] Nothing)) variances
    tcM = M.union (M.mapWithKey (\c -> mkRTyCon (M.findWithDefault [] c variances)) declarations) defaults
    -- An authored invariant restricts transport in both directions; it is not
    -- evidence of an absent occurrence. Keeping that restriction compositional
    -- can conservatively reject positivity through an invariant wrapper.
    restriction Invariant = Bivariant
    restriction v = v
    tcInstM = mkFInstRTyCon tce fiTcs tcM
    arities =
      foldr
        (\(c, a) -> M.insertWith (checkEqValues c) c a)
        M.empty
        [(c, length ts) | (c, ts) <- M.keys tcInstM]

    checkEqValues c v0 v1 =
      if v0 == v1
        then v0
        else
          panic Nothing $
            "makeTyConInfo: Conflicting arities for TyCon: "
              ++ showPpr c
              ++ " "
              ++ showPpr v0
              ++ " "
              ++ showPpr v1

mkFInstRTyCon :: F.TCEmb Ghc.TyCon -> [Ghc.TyCon] -> M.HashMap Ghc.TyCon RTyCon -> M.HashMap (Ghc.TyCon, [F.Sort]) RTyCon
mkFInstRTyCon tce fiTcs tcm =
    M.fromList
        [ ((c, typeSort tce <$> ts), rtc)
        | fiTc <- fiTcs
        , rtc <- Mb.maybeToList (M.lookup fiTc tcm)
        , (c, ts) <- Mb.maybeToList (famInstArgs fiTc)
        , M.member c predicateFamilies
        ]
  where
    -- This map selects predicate parameters, not representation equalities.
    -- Omit only whole families with no predicates: an empty instance may
    -- override origin predicates, and mixed families must retain every key.
    predicateFamilies =
        M.fromList
            [ (maybe tc fst (Ghc.tyConFamInst_maybe tc), ())
            | (tc, rtc) <- M.toList tcm
            , not (null (rTyConPVs rtc))
            ]

mkRTyCon :: VarianceInfo -> TyConP -> RTyCon
mkRTyCon tyvariance (TyConP _ tc αs' ps _ predvariance size) =
  RTyCon tc pvs' (TyConInfo tyvariance predvariance size)
  where
    τs = [rVar α :: RSort | α <- tyConTyVarsDef tc]
    pvs' = subts (zip αs' τs) <$> ps


-------------------------------------------------------------------------------
{- | @dataConPSpecType@ converts a @DataConP@, LH's internal representation for
  a (refined) data constructor into a @SpecType@ for that constructor.
  TODO: duplicated with Liquid.Measure.makeDataConType
-}

-------------------------------------------------------------------------------
dataConPSpecType :: (CoreExpr -> (F.Expr, LogicSupport)) -> M.HashMap DataCon ConstructorBox -> Bool -> DataConP -> ([(Var, SpecType)], LogicSupport)
-------------------------------------------------------------------------------
dataConPSpecType interpret boxes allowTC dcp = ([(workX, workT), (wrapX, wrapT)], support)
  where
    wrapT
        | Mb.isNothing (Measure.constructorSourceMatch dc sourceT) =
            Ex.throw
                ( ErrDataCon
                    (fSrcSpan dcp)
                    (F.pprint dc)
                    ( Pretty.text "source constructor contract does not match GHC carrier"
                        Pretty.$$ (Pretty.text "Declared:" Pretty.<+> F.pprint sourceT)
                        Pretty.$$ (Pretty.text "GHC carrier:" Pretty.<+> F.pprint (varType wrapX))
                    ) ::
                    Error
                )
        | otherwise = sourceT
    (workT, support)
        | workX == wrapX = (wrapT, [])
        | eqType (varType workX) (toType False wrapT) = (wrapT, [])
        | all isTauto wrapT && null (ty_preds (toRTypeRep wrapT)) = (ofType (varType workX), [])
        | otherwise = Measure.constructorWorkerType interpret boxes dc wrapT
    sourceT = dcWrapSpecType allowTC dc dcp
    workX = dataConWorkId dc -- This is the weird one for GADTs
    wrapX = dataConWrapId dc -- This is what the user expects to see
    dc = dcpCon dcp

-- Runtime dictionaries precede declared fields in the actual constructor.
-- Class constructors already carry their superclasses in dcpTyArgs; plugging
-- leaves their dcpTyConstrs empty. Primitive equality evidence has no value
-- coordinate. Keep this order shared by declarations and their projections.
dataConRuntimeFields :: DataConP -> [(LHName, SpecType)]
dataConRuntimeFields dcp = dictionaries ++ reverse (dcpTyArgs dcp)
 where
  dictionaries =
    [ (makeGeneratedLogicLHName (F.intSymbol prefix i), t)
    | (i, t) <- zip [1 ..] (filter (not . isEmbeddedDictType . toType False) (dcpTyConstrs dcp))
    ]
  prefix = F.suffixSymbol (F.symbol $ dcpCon dcp) "lq$dictionary"


dataConWorkRep :: DataCon -> SpecRep
dataConWorkRep c = toRTypeRep
                 -- . F.tracepp ("DCWR-2: " ++ F.showpp c)
                 . ofType
                 -- . F.tracepp ("DCWR-1: " ++ F.showpp c)
                 . dataConRepType
                 -- . Var.varType
                 -- . dataConWorkId
                 $ c


-- maybe a tc flag is unnecessary but I don't know if {-@ class ... @-}
-- would reach here
dcWrapSpecType :: Bool -> DataCon -> DataConP -> SpecType
dcWrapSpecType allowTC dc (DataConP _ _ vs ps cs yts rt _ _ _)
  = {- F.tracepp ("dcWrapSpecType: " ++ show dc ++ " " ++ F.showpp rt) $ -}
    mkArrow makeVars' ps ts' rt'
  where
    isCls    = Ghc.isClassTyCon $ Ghc.dataConTyCon dc
    (as0, sts) = unzip (reverse yts)
    as = map lhNameToResolvedSymbol as0
    as1 = map lhNameToUnqualifiedSymbol as0
    mkDSym z = F.symbol z `F.suffixSymbol` F.symbol dc
    bs       = mkDSym <$> as
    tx _  []     []     []     = []
    tx su (x:xs) (y:ys) (t:ts) = (y, classRFInfo allowTC , if allowTC && isCls then t else F.subst (F.mkSubst su) t, mempty)
                               : tx ((x, F.EVar y):su) xs ys ts
    tx _ _ _ _ = panic Nothing "PredType.dataConPSpecType.tx called on invalid inputs"
    yts'     = tx [] as1 bs sts
    ts'      = map ("" , classRFInfo allowTC , , mempty) cs ++ yts'
    subst    = F.mkSubst [(x, F.EVar y) | (x, y) <- zip as1 bs]
    rt'      = F.subst subst rt
    makeVars = filter (`elem` fvs) $ zipWith (\v a -> RTVar v (rTVarInfo a)) vs (fst $ splitForAllTyCoVars $ dataConRepType dc)
    makeVars' = map (, mempty) makeVars
    fvs = freeTyVars $ mkArrow [] ps ts' rt'

dataConTy :: IsReft r
          => M.HashMap RTyVar (RType RTyCon RTyVar r)
          -> Type -> RType RTyCon RTyVar r
dataConTy m (TyVarTy v)
  = M.lookupDefault (rVar v) (RTV v) m
dataConTy m (FunTy _ _ t1 t2)
  = rFun F.dummySymbol (dataConTy m t1) (dataConTy m t2)
dataConTy m (ForAllTy (Bndr α _) t) -- α :: TyVar
  = RAllT (makeRTVar (RTV α)) (dataConTy m t) trueReft
dataConTy m (TyConApp c ts)
  = rApp c (dataConTy m <$> ts) [] trueReft
dataConTy _ _
  = panic Nothing "ofTypePAppTy"

----------------------------------------------------------------------------
-- | Interface: Replace Predicate With Uninterpreted Function Symbol -------
----------------------------------------------------------------------------
replacePredsWithRefs :: (UsedPVar, (F.Symbol, [(NoReft, F.Symbol, F.Expr)]) -> F.Expr)
                     -> UReft -> UReft
replacePredsWithRefs (p, r) (MkUReft (F.Reft(v, rs)) (Pr ps))
  = MkUReft (F.Reft (v, rs'')) (Pr ps2)
  where
    rs''             = foldr (F.&.&) F.PTrue $ rs : rs'
    rs'              = r . (v,) . pargs <$> ps1
    (ps1, ps2)       = L.partition (== p) ps

pVartoRConc :: PVar t -> (F.Symbol, [(a, b, F.Expr)]) -> F.Expr
pVartoRConc p (v, args) | length args == length (pargs p)
  = pApp (pname p) $ F.EVar v : (thd3 <$> args)

pVartoRConc p (v, args)
  = pApp (pname p) $ F.EVar v : args'
  where
    args' = (thd3 <$> args) ++ drop (length args) (thd3 <$> pargs p)

-----------------------------------------------------------------------
-- | @pvarRType π@ returns a trivial @RType@ corresponding to the
--   function signature for a @PVar@ @π@. For example, if
--      @π :: T1 -> T2 -> T3 -> Prop@
--   then @pvarRType π@ returns an @RType@ with an @RTycon@ called
--   @predRTyCon@ `RApp predRTyCon [T1, T2, T3]`
-----------------------------------------------------------------------
pvarRType :: (PPrint r, IsReft r) => PVar RSort -> RRType r
-----------------------------------------------------------------------
pvarRType (PV _ k {- (PVProp τ) -} args) = rpredType k (fst3 <$> args) -- (ty:tys)
  -- where
  --   ty  = uRTypeGen τ
  --   tys = uRTypeGen . fst3 <$> args

rpredType :: IsReft r
          => RType RTyCon tv a
          -> [RType RTyCon tv a] -> RType RTyCon tv r
rpredType t ts = RApp predRTyCon  (uRTypeGen <$> t : ts) [] trueReft

predRTyCon   :: RTyCon
predRTyCon   = symbolRTyCon predName

symbolRTyCon   :: F.Symbol -> RTyCon
symbolRTyCon n = RTyCon (stringTyCon 'x' 42 $ F.symbolString n) [] defaultTyConInfo

-------------------------------------------------------------------------------------
-- | Instantiate `PVar` with `RTProp` -----------------------------------------------
-------------------------------------------------------------------------------------
-- | @replacePreds@ is the main function used to substitute an (abstract)
--   predicate with a concrete Ref, that is either an `RProp` or `RHProp`
--   type. The substitution is invoked to obtain the `SpecType` resulting
--   at /predicate application/ sites in 'Language.Haskell.Liquid.Constraint'.
--   The range of the `PVar` substitutions are /fresh/ or /true/ `RefType`.
--   That is, there are no further _quantified_ `PVar` in the target.
-------------------------------------------------------------------------------------
replacePreds                 :: String -> SpecType -> [(RPVar, SpecProp)] -> SpecType
-------------------------------------------------------------------------------------
replacePreds msg                 = L.foldl' go
  where
     go _ (_, RProp _ (RHole _)) = panic Nothing "replacePreds on RProp _ (RHole _)"
     go z (π, t)                 = substPred msg   (π, t)     z


-- TODO: replace `replacePreds` with
-- instance SubsTy RPVar (Ref RReft SpecType) SpecType where
--   subt (pv, r) t = replacePreds "replacePred" t (pv, r)

-- replacePreds :: String -> SpecType -> [(RPVar, Ref Reft RefType)] -> SpecType
-- replacePreds msg       = foldl' go
--   where go z (π, RProp t) = substPred msg   (π, t)     z
--         go z (π, RPropP r) = replacePVarReft (π, r) <$> z

-------------------------------------------------------------------------------------
substPVar :: PVarV v (BSortV v) -> PVarV v (BSortV v) -> BareTypeParsed -> BareTypeParsed
-------------------------------------------------------------------------------------
substPVar src dst = go
  where
    go :: BareTypeParsed -> BareTypeParsed
    go (RVar a r)         = RVar a (goRR r)
    go (RApp c ts rs r)   = RApp c (go <$> ts) (goR <$> rs) (goRR r)
    go (RAllP q t)
     | pname q == pname src = RAllP q t
     | otherwise            = RAllP q (go t)
    go (RAllT a t r)      = RAllT a   (go t)  (goRR r)
    go (RFun x i t t' r)  = RFun x i  (go t)  (go t') (goRR r)
    go (REx x t t')       = REx x     (go t)  (go t')
    go (RRTy e r o rt)    = RRTy e'   (goRR r) o (go rt) where e' = [(x, go t) | (x, t) <- e]
    go (RAppTy t1 t2 r)   = RAppTy    (go t1) (go t2) (goRR r)
    go (RHole r)          = RHole     (goRR r)
    go t@(RLit _)        = t
    go t@(RExprArg  _)    = t
    goR :: BRPropV LocSymbol (RReftV LocSymbol) -> BRPropV LocSymbol (RReftV LocSymbol)
    goR rp = rp {rf_body = go (rf_body rp) }
    goRR :: RReftV LocSymbol -> RReftV LocSymbol
    goRR rr = rr { ur_pred = goP (ur_pred rr) }
    goP :: PredicateV LocSymbol -> PredicateV LocSymbol
    goP (Pr ps) = Pr (goPV <$> ps)
    goPV :: UsedPVarV LocSymbol -> UsedPVarV LocSymbol
    goPV pv
      | pname pv == pname src = pv { pname = pname dst }
      | otherwise             = pv

-------------------------------------------------------------------------------
substPred :: String -> (RPVar, SpecProp) -> SpecType -> SpecType
-------------------------------------------------------------------------------

substPred _   (rp, RProp ss (RVar a1 r1)) t@(RVar a2 r2)
  | isPredInReft && a1 == a2    = RVar a1 $ meetListWithPSubs (thd3 <$> pargs rp) πs ss r1 r2'
  | isPredInReft                = panic Nothing ("substPred RVar Var Mismatch" ++ show (a1, a2))
  | otherwise                   = t
  where
    (r2', πs)                   = splitRPvar rp r2
    isPredInReft                = not $ null πs

substPred msg su@(π, _ ) (RApp c ts rs r)
  | null πs                     = t'
  | otherwise                   = substRCon msg su t' πs r2'
  where
    t'                          = RApp c (substPred msg su <$> ts) (substPredP msg su <$> rs) r
    (r2', πs)                   = splitRPvar π r

substPred msg (p, tp) (RAllP q@PV{} t)
  | p /= q                      = RAllP q $ substPred msg (p, tp) t
  | otherwise                   = RAllP q t

substPred msg su (RAllT a t r)  = RAllT a (substPred msg su t) r

substPred msg su@(rp,prop) (RFun x i rt rt' r)
--                        = RFun x (substPred msg su t) (substPred msg su t') r
  | null πs                     = RFun x i (substPred msg su rt) (substPred msg su rt') r
  | otherwise                   =
      let sus = (\π -> F.mkSubst (zip (fst <$> rf_args prop) (thd3 <$> pargs π))) <$> πs in
      foldl (\t subst -> t `meet` F.subst subst (rf_body prop)) (RFun x i (substPred msg su rt) (substPred msg su rt') r') sus
  where (r', πs)                = splitRPvar rp r
-- ps has   , pargs :: ![(t, Symbol, Expr)]

substPred msg su (RRTy e r o t) = RRTy (fmap (substPred msg su) <$> e) r o (substPred msg su t)
substPred msg su (REx x t t')   = REx   x (substPred msg su t) (substPred msg su t')
substPred _   _  t              = t

-- | Requires: @not $ null πs@
-- substRCon :: String -> (RPVar, SpecType) -> SpecType -> SpecType

substRCon :: String -> (RPVar, SpecProp) -> SpecType -> [UsedPVar] -> UReft -> SpecType
substRCon msg (rp, RProp ss t1@(RApp c1 ts1 rs1 r1)) t2@(RApp c2 ts2 rs2 _) πs r2'
    | rtc_tc c1 == rtc_tc c2 = RApp c1 ts rs $ meetListWithPSubs defaults πs ss r1 r2'
  where
    defaults = thd3 <$> pargs rp
    ts = F.subst su $ safeZipWith (msg ++ ": substRCon") strSub ts1 ts2
    rs = F.subst su $ safeZipWith (msg ++ ": substRCon2") strSubR rs1' rs2'
    (rs1', rs2') = pad "substRCon" top rs1 rs2
    strSub x r2 = meetListWithPSubs defaults πs ss x r2
    strSubR x r2 = meetListWithPSubsRef πs ss x r2

    su = F.mkSubst $ zipWith (\s1 s2 -> (s1, F.EVar s2)) (rvs t1) (rvs t2)

    rvs = foldReft False (\_ r acc -> rvReft r : acc) []
    rvReft r = let F.Reft (s, _) = toReft r in s

substRCon msg su t _ _        = {- panic Nothing -} errorP "substRCon: " $ msg ++ " " ++ showpp (su, t)

pad :: [Char] -> (a -> a) -> [a] -> [a] -> ([a], [a])
pad _ f [] ys   = (f <$> ys, ys)
pad _ f xs []   = (xs, f <$> xs)
pad msg _ xs ys
  | nxs == nys  = (xs, ys)
  | otherwise   = panic Nothing $ "pad: " ++ msg
  where
    nxs         = length xs
    nys         = length ys

substPredP :: [Char]
           -> (RPVar, Ref RSort (RRType RReft))
           -> Ref RSort (RType RTyCon RTyVar RReft)
           -> Ref RSort SpecType
substPredP _ su p@(RProp _ (RHole _))
  = panic Nothing ("PredType.substPredP1 called on invalid inputs: " ++ showpp (su, p))
substPredP msg (p, RProp ss prop) (RProp s t)
  = RProp ss' $ substPred (msg ++ ": substPredP") (p, RProp ss {- (subst su prop) -} prop ) t
 where
   ss' = drop n ss ++  s
   n   = length ss - length (freeArgsPs p t)
   -- su  = mkSubst (zip (fst <$> ss) (EVar . fst <$> ss'))


splitRPvar :: PVar t -> UReft -> (UReft, [UsedPVar])
splitRPvar pv (MkUReft x (Pr pvs)) = (MkUReft x (Pr pvs'), epvs)
  where
    (epvs, pvs')               = L.partition (uPVar pv ==) pvs

-- TODO: rewrite using foldReft
freeArgsPs :: PVar (RType t t1 NoReft) -> RType t t1 UReft -> [F.Symbol]
freeArgsPs p (RVar _ r)
  = freeArgsPsRef p r
freeArgsPs p (RFun _ _ t1 t2 r)
  = L.nub $  freeArgsPsRef p r ++ freeArgsPs p t1 ++ freeArgsPs p t2
freeArgsPs p (RAllT _ t r)
  = L.nub $  freeArgsPs p t ++ freeArgsPsRef p r
freeArgsPs p (RAllP p' t)
  | p == p'   = []
  | otherwise = freeArgsPs p t
freeArgsPs p (RApp _ ts _ r)
  = L.nub $ freeArgsPsRef p r ++ concatMap (freeArgsPs p) ts
freeArgsPs p (REx _ t1 t2)
  = L.nub $ freeArgsPs p t1 ++ freeArgsPs p t2
freeArgsPs p (RAppTy t1 t2 r)
  = L.nub $ freeArgsPsRef p r ++ freeArgsPs p t1 ++ freeArgsPs p t2
freeArgsPs _ (RLit _)
  = []
freeArgsPs _ (RExprArg _)
  = []
freeArgsPs p (RHole r)
  = freeArgsPsRef p r
freeArgsPs p (RRTy env r _ t)
  = L.nub $ concatMap (freeArgsPs p . snd) env ++ freeArgsPsRef p r ++ freeArgsPs p t

freeArgsPsRef :: PVar t1 -> UReft -> [F.Symbol]
freeArgsPsRef p (MkUReft _ (Pr ps)) = [x | (_, x, w) <- concatMap pargs ps', F.EVar x == w]
  where
   ps' = f <$> filter (uPVar p ==) ps
   f q = q {pargs = pargs q ++ drop (length (pargs q)) (pargs $ uPVar p)}

meetListWithPSubs ::
    (Foldable t, PPrint t1, F.Subable b, F.Variable b ~ F.Symbol, Meet b) =>
    [F.Expr] -> t (PVar t1) -> [(F.Symbol, RSort)] -> b -> b -> b
meetListWithPSubs defaults πs ss r1 r2 = L.foldl' (meetListWithPSub defaults ss r1) r2 πs

meetListWithPSubsRef
  :: ( Foldable t
     , Meet (RType c tv r)
     , TyConable c
     , IsReft r
     , F.Subable r
     , F.Variable r ~ F.Symbol
     , ReftBind r ~ F.Symbol
     , ReftVar r ~ F.Symbol
     )
  => t (PVar t4)
  -> [(F.Symbol, b)]
  -> Ref τ (RType c tv r)
  -> Ref τ (RType c tv r)
  -> Ref τ (RType c tv r)
meetListWithPSubsRef πs ss r1 r2 = L.foldl' (meetListWithPSubRef ss r1) r2 πs

meetListWithPSub :: (PPrint t, F.Subable r, F.Variable r ~ F.Symbol, Meet r) => [F.Expr] -> [(F.Symbol, RSort)] -> r -> r -> PVar t -> r
meetListWithPSub defaults ss r1 r2 π
    | length supplied <= length defaults && length actuals == length ss =
        r2 `meet` F.subst (F.mkSubst (zip (fst <$> ss) actuals)) r1
    | otherwise =
        panic Nothing $ "PredType.meetListWithPSub argument arity mismatch: " ++ showpp π
  where
    supplied = thd3 <$> pargs π
    actuals = supplied ++ drop (length supplied) defaults

meetListWithPSubRef
  :: ( Meet (RType c tv r)
     , TyConable c
     , IsReft r
     , F.Subable r
     , F.Variable r ~ F.Symbol
     , ReftBind r ~ F.Symbol
     , ReftVar r ~ F.Symbol
     )
 => [(F.Symbol, b)]
 -> Ref τ (RType c tv r)
 -> Ref τ (RType c tv r)
 -> PVar t3
 -> Ref τ (RType c tv r)
meetListWithPSubRef _ (RProp _ (RHole _)) _ _ -- TODO: Is this correct?
  = panic Nothing "PredType.meetListWithPSubRef called with invalid input"
meetListWithPSubRef _ _ (RProp _ (RHole _)) _
  = panic Nothing "PredType.meetListWithPSubRef called with invalid input"
meetListWithPSubRef ss (RProp s1 r1) (RProp s2 r2) π
    | all (\(_, x, F.EVar y) -> x == y) (pargs π) =
        RProp s1 $ F.subst su' r2 `meet` r1
    | all (\(_, x, F.EVar y) -> x /= y) (pargs π) =
        -- Keep the nested relation's dependencies under the retained telescope
        -- before substituting the enclosing predicate's actual arguments.
        RProp s2 $ r2 `meet` F.subst su (F.subst align r1)
    | otherwise =
        panic Nothing $ "PredType.meetListWithPSubRef partial application to " ++ showpp π
  where
    su = F.mkSubst [(x, y) | (x, (_, _, y)) <- zip (fst <$> ss) (pargs π)]
    su' = F.mkSubst [(x, F.EVar y) | (x, y) <- zip (fst <$> s2) (fst <$> s1)]
    align = F.mkSubst [(x, F.EVar y) | (x, y) <- zip (fst <$> s1) (fst <$> s2)]


----------------------------------------------------------------------------
-- | Interface: Modified CoreSyn.exprType due to predApp -------------------
----------------------------------------------------------------------------
predType   :: Type
predType   = symbolType predName

predName :: F.Symbol
predName   = "Pred"

symbolType :: F.Symbol -> Type
symbolType = TyVarTy . symbolTyVar


substParg :: Functor f => (F.Symbol, F.Expr) -> f Predicate -> f Predicate
substParg (x, y) = fmap fp
  where
    fxy s        = if s == F.EVar x then y else s
    fp           = subvPredicate (\pv -> pv { pargs = mapThd3 fxy <$> pargs pv })

-------------------------------------------------------------------------------
-----------------------------  Predicate Application --------------------------
-------------------------------------------------------------------------------
pappArity :: Int
pappArity  = 7

pappSort :: Int -> F.Sort
pappSort n = F.mkFFunc (2 * n) $ [ptycon] ++ args ++ [F.boolSort]
  where
    ptycon = F.fAppTC predFTyCon $ F.FVar <$> [0..n-1]
    args   = F.FVar <$> [n..(2*n-1)]


predFTyCon :: F.FTycon
predFTyCon = F.symbolFTycon $ dummyLoc predName
