{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TypeOperators         #-}

{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

-- | Constraint Splitting ------------------------------------------------------
--
-- Constraint splitting is the process of decomposing high-level subtyping
-- constraints between LiquidHaskell refinement types into low-level Horn
-- clauses that the Liquid Fixpoint solver can check.
--
-- A subtyping constraint @t1 <: t2@ between two 'SpecType' values is created
-- during constraint generation (Generate.hs) whenever LH needs to verify that
-- one type is a subtype of another (e.g., function argument vs. parameter type,
-- branch types, etc.). These constraints are represented as @SubC γ t1 t2@
-- where @γ@ is the typing environment.
--
-- 'splitC' recursively walks the structure of @t1@ and @t2@ simultaneously,
-- peeling off type constructors until it reaches base refinements, at which
-- point it calls 'bsplitC' to emit a fixpoint `SubC`
-- (a Horn clause of the form @∀ binds. lhs-reft ⟹ rhs-reft@).
--

module Language.Haskell.Liquid.Constraint.Split (

  -- * Split Subtyping Constraints
    splitC
  , splitCWith
  , splitCheckedCWith
  , substCheckedTyVar
  , bsplitC

  -- * Split Well-formedness Constraints
  , splitW

  -- * ???
  , envToSub

  -- * Panic
  , panicUnbound
  ) where

import           Prelude hiding (error)



import           Text.PrettyPrint.HughesPJ hiding (first, parens)

import           Data.Maybe          (fromMaybe)
import           Control.Monad
import           Control.Monad.State (gets)
import qualified Control.Exception as Ex

import qualified Language.Fixpoint.Types            as F
import qualified Data.HashSet as S
import           Language.Fixpoint.Misc hiding (errorstar)
import           Language.Fixpoint.SortCheck (pruneUnsortedReft)

import           Language.Haskell.Liquid.Misc -- (concatMapM)
import qualified Language.Haskell.Liquid.UX.CTags       as Tg
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.Fresh
import           Language.Haskell.Liquid.Types.PredType
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.UX.Config
import           Language.Haskell.Liquid.UX.Tidy ()


import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Constraint.Env
import           Language.Haskell.Liquid.Constraint.Constraint
import           Language.Haskell.Liquid.Constraint.Monad (envToSub, freshPredRef, addPToEnv)

--------------------------------------------------------------------------------
splitW ::  WfC -> CG [FixWfC]
--------------------------------------------------------------------------------
splitW (WfC γ t@(RFun x _ t1 t2 _))
  =  do ws'  <- splitW (WfC γ t1)
        γ'   <- γ += ("splitW", x, t1)
        ws   <- bsplitW γ t
        ws'' <- splitW (WfC γ' t2)
        return $ ws ++ ws' ++ ws''

splitW (WfC γ t@(RAppTy t1 t2 _))
  =  do ws   <- bsplitW γ t
        ws'  <- splitW (WfC γ t1)
        ws'' <- splitW (WfC γ t2)
        return $ ws ++ ws' ++ ws''

splitW (WfC γ t'@(RAllT a t _))
  = do γ'  <- updateEnv γ a
       ws  <- bsplitW γ t'
       ws' <- splitW (WfC γ' t)
       return $ ws ++ ws'

splitW (WfC γ (RAllP _ r))
  = splitW (WfC γ r)

splitW (WfC γ t@(RVar _ _))
  = bsplitW γ t

splitW (WfC γ t@(RApp _ ts rs _))
  =  do ws    <- bsplitW γ t
        γ'    <- if bscope (getConfig γ) then γ `extendEnvWithVV` t else return γ
        ws'   <- concat <$> mapM (splitW . WfC γ') ts
        ws''  <- concat <$> mapM (rsplitW γ)       rs
        return $ ws ++ ws' ++ ws''

splitW (WfC γ (REx x tx t))
  = do  ws  <- splitW (WfC γ tx)
        γ'  <- γ += ("splitW2", x, tx)
        ws' <- splitW (WfC γ' t)
        return $ ws ++ ws'

splitW (WfC γ (RRTy _ _ _ t))
  = splitW (WfC γ t)

splitW (WfC _ (RLit _))
  = return []

splitW (WfC _ t)
  = panic Nothing $ "splitW cannot handle: " ++ showpp t

rsplitW :: CGEnv
        -> Ref RSort SpecType
        -> CG [FixWfC]
rsplitW _ (RProp _ (RHole _)) =
  panic Nothing "Constrains: rsplitW for RProp _ (RHole _)"

rsplitW γ (RProp ss t0) = do
  γ' <- foldM (+=) γ [("rsplitW", x, ofRSort s) | (x, s) <- ss]
  splitW $ WfC γ' t0


bsplitW :: CGEnv -> SpecType -> CG [FixWfC]
bsplitW γ t =
  do temp  <- getTemplates
     isHO  <- gets allowHO
     return $ bsplitW' γ t temp isHO

bsplitW' :: (PPrint r, IsReft r, ReftBind r ~ F.Symbol, ReftVar r ~ F.Symbol, SubsTy RTyVar RSort r)
         => CGEnv -> RRType r -> F.Templates -> Bool -> [F.WfC Cinfo]
bsplitW' γ t temp isHO
  | isHO || F.isNonTrivial r'
  = F.wfC (feBinds $ fenv γ) r' ci
  | otherwise
  = []
  where
    r'                = rTypeSortedReft' γ temp t
    ci                = Ci (getLocation γ) Nothing (cgVar γ)

splitfWithVariance :: Applicative f
                   => (t -> t -> f [a]) -> t -> t -> Variance -> f [a]
splitfWithVariance f t1 t2 Invariant     = (++) <$> f t1 t2 <*> f t2 t1
splitfWithVariance f t1 t2 Bivariant     = (++) <$> f t1 t2 <*> f t2 t1
splitfWithVariance f t1 t2 Covariant     = f t1 t2
splitfWithVariance f t1 t2 Contravariant = f t2 t1

updateEnv :: CGEnv -> RTVar F.Symbol F.Symbol RTyCon RTyVar -> CG CGEnv
updateEnv γ a
  | Just (x, s) <- rTVarToBind a
  = γ += ("splitS RAllT", x, fmap (const mempty) s)
  | otherwise
  = return γ

------------------------------------------------------------
splitC :: Bool -> SubC -> CG [FixSubC]
------------------------------------------------------------
splitC = splitCWith bsplitC

-- The emitter observes the judgment at the same leaf, in the same oriented
-- environment, as ordinary refinement subtyping. In particular, callback
-- domains reverse the endpoints and result environments retain RHS domains.
splitCWith :: (CGEnv -> SpecType -> SpecType -> CG [FixSubC]) -> Bool -> SubC -> CG [FixSubC]
splitCWith emit allowTC constraint = splitCheckedCWith (\_ environment left right -> emit environment (ordinarySpecType left) (ordinarySpecType right)) allowTC paired
  where
    paired = case constraint of
        SubC environment left right -> SubC environment (logicalSpecType left) (logicalSpecType right)
        SubR environment obligation refinement -> SubR environment obligation refinement

-- Source formation interprets concrete terms, not abstract Pr applications.
-- Keep those term denotations unchanged while transporting the owned Pr
-- contracts; the actual native leaf lowers them after query composition.
renamePredicate :: RPVar -> RPVar -> CheckedRefinement -> CheckedRefinement
renamePredicate source destination refinement = refinement{checkedLogical = renameLogical (checkedLogical refinement), checkedPredicates = map renameQuery (checkedPredicates refinement)}
  where
    renameLogical logical = logical{ur_pred = Pr (map rename applications)}
      where
        Pr applications = ur_pred logical
    rename application
        | pname application == pname source = application{pname = pname destination}
        | otherwise = application
    renameQuery query =
        query
            { predicateSignature = mapScopedPredicateWith scopeBinder source (const renameLogical) (predicateSignature query)
            }
    scopeBinder binder
        | pname binder == pname source = Just (binder{pname = pname destination}, pname destination)
        | otherwise = Just (binder, pname binder)

instantiatePredicateQueries :: RPVar -> [(F.Symbol, RSort)] -> UReft -> CheckedRefinement -> CheckedRefinement
instantiatePredicateQueries predicate formals replacement refinement =
    refinement{checkedPredicates = map instantiateQuery (checkedPredicates refinement)}
  where
    instantiateQuery query =
        query
            { predicateSignature = substPredAtomicWith scopeBinder id id (\logical _ -> logical) meet "splitC query" predicate formals replacement (predicateSignature query)
            }
    scopeBinder binder
        | pname binder == pname predicate = Nothing
        | otherwise = Just (binder, pname binder)

concretizePredicate :: RPVar -> CheckedRefinement -> CheckedRefinement
concretizePredicate predicate refinement =
    refinement
        { checkedLogical = concrete (checkedLogical refinement)
        }
  where
    concrete = replacePredsWithRefs (uPVar predicate, pVartoRConc predicate)

shiftCheckedVV :: CheckedSpecType -> F.Symbol -> CheckedSpecType
shiftCheckedVV = shiftVVWith (F.reftBind . ur_reft . checkedOrdinary . rootRefinement) renameCheckedRoot types props
  where
    rootRefinement ty = case stripRTypeBase ty of
        Just refinement -> refinement
        Nothing -> CheckedRefinement mempty []
    types tys binding = map (rTypeSubstWith (Just . F.reftBind . ur_reft . checkedOrdinary) names action) tys
      where
        action = F.mkSubst [binding]
        names = F.substSymbolsSet action `S.union` S.unions (map checkedTypeSyms tys)
    props refinements binding = map (refSubstWith (rTypeSubstWith (Just . F.reftBind . ur_reft . checkedOrdinary)) names action) refinements
      where
        action = F.mkSubst [binding]
        names = F.substSymbolsSet action `S.union` S.unions (map (checkedTypeSyms . rf_body) refinements)

substCheckedTyVar :: (RTyVar, RTyVar) -> CheckedSpecType -> CheckedSpecType
substCheckedTyVar (source, destination) = subsFreeWith Nothing preserveBound transport meetCheckedRefinement (const checkedTop) (isTauto . checkedOrdinary) True S.empty (source, RVar destination NoReft, RVar destination checkedTop)
  where
    checkedTop = CheckedRefinement mempty []
    preserveBound substitution binder = (subt substitution binder, ty_var_value binder)
    transport substitution@(variable, replacement) refinement = case replacement of
        RVar (RTV target) _ ->
            refinement{checkedLogical = subt substitution (checkedLogical refinement), checkedPredicates = map (renameType variable target) (checkedPredicates refinement)}
        _ -> CheckedRefinement (subt substitution (checkedOrdinary refinement)) []
    renameType variable@(RTV original) target checked =
        checked
            { predicateSignature = renameQueryCoordinate variable (RTV target) (predicateSignature checked)
            , predicateReadback = subt (variable, RVar (RTV target) NoReft :: RSort) (predicateReadback checked)
            , predicateTelescope = (predicateTelescope checked){queryTypeOwners = [(transportOwner owner, native) | (owner, native) <- queryTypeOwners (predicateTelescope checked)]}
            , predicateDefinitions = [(owner, subt (variable, RVar (RTV target) NoReft :: RSort) meaning) | (owner, meaning) <- predicateDefinitions checked]
            , predicateSupport = [(owner, subt (variable, RVar (RTV target) NoReft :: RSort) sort) | (owner, sort) <- predicateSupport checked]
            }
      where
        transportOwner owner
            | owner == original = target
            | RTV transported <- subt (variable, RVar (RTV target) NoReft :: RSort) (RTV owner) = transported
    renameQueryCoordinate :: RTyVar -> RTyVar -> SpecType -> SpecType
    renameQueryCoordinate variable target =
        subsFreeWith Nothing renameBound subt meet top isTauto True S.empty (variable, RVar target NoReft, RVar target mempty)
      where
        renameBound substitution@(coordinate, replacement) binder =
            let transported = subt substitution binder
             in case replacement of
                    RVar renamed _
                        | ty_var_value binder == coordinate ->
                            (transported{ty_var_value = renamed}, renamed)
                    _ -> (transported, ty_var_value binder)

-- The emitter receives only rigid owners introduced in this lexical split.
-- Capturing introductions in its continuation preserves their branch scope.
splitCheckedCWith :: ([RPVar] -> CGEnv -> CheckedSpecType -> CheckedSpecType -> CG [FixSubC]) -> Bool -> SubCWith CheckedRefinement -> CG [FixSubC]
splitCheckedCWith emit allowTC (SubC γ (REx x tx t1) (REx x2 _ t2)) | x == x2 =
    do
        γ' <- γ += ("addExBind 0", x, forallExprRefType γ (ordinarySpecType tx))
        splitCheckedCWith emit allowTC (SubC γ' t1 t2)
splitCheckedCWith emit allowTC (SubC γ t1 (REx x tx t2)) =
    do
        y <- fresh
        γ' <- γ += ("addExBind 1", y, forallExprRefType γ (ordinarySpecType tx))
        splitCheckedCWith emit allowTC (SubC γ' t1 (substCheckedType (F.mkSubst [(x, F.EVar y)]) t2))

-- existential at the left hand side is treated like forall
splitCheckedCWith emit allowTC (SubC γ (REx x tx t1) t2) =
    do
        -- let tx' = traceShow ("splitC allowTC: " ++ showpp z) tx
        y <- fresh
        γ' <- γ += ("addExBind 2", y, forallExprRefType γ (ordinarySpecType tx))
        splitCheckedCWith emit allowTC (SubC γ' (substCheckedType (F.mkSubst [(x, F.EVar y)]) t1) t2)
splitCheckedCWith emit allowTC (SubC cgenv (RRTy env _ OCons t1) t2) =
    do
        γ' <- foldM (\γ (x, t) -> γ `addSEnv` ("splitS", x, ordinarySpecType t)) cgenv xts
        c1 <- splitCheckedCWith emit allowTC (SubC γ' t1' t2')
        c2 <- splitCheckedCWith emit allowTC (SubC cgenv t1 t2)
        return $ c1 ++ c2
  where
    (xts, t1', t2') = envToSub env
splitCheckedCWith emit allowTC (SubC cgenv (RRTy e r o t1) t2) =
    do
        γ' <- foldM (\γ (x, t) -> γ `addSEnv` ("splitS", x, ordinarySpecType t)) cgenv e
        c1 <- splitCheckedCWith emit allowTC (SubR γ' o (checkedOrdinary r))
        c2 <- splitCheckedCWith emit allowTC (SubC cgenv t1 t2)
        return $ c1 ++ c2
splitCheckedCWith emit allowTC (SubC γ (RFun x1 i1 t1 t1' r1) (RFun x2 i2 t2 t2' r2)) =
    do
        cs' <- splitCheckedCWith emit allowTC (SubC γ t2 t1)
        γ' <- γ += ("splitC allowTC", x2, ordinarySpecType t2)
        cs <-
            emit
                []
                γ
                (RFun x1 i1 t1 t1' (r1 `F.subst1` (x1, F.EVar x2)))
                (RFun x2 i2 t2 t2' r2)
        let t1x2' = substCheckedType (F.mkSubst [(x1, F.EVar x2)]) t1'
        cs'' <- splitCheckedCWith emit allowTC (SubC γ' t1x2' t2')
        return $ cs ++ cs' ++ cs''
splitCheckedCWith emit allowTC (SubC γ t1@(RAppTy r1 r1' _) t2@(RAppTy r2 r2' _)) =
    do
        cs <- emit [] γ t1 t2
        cs' <- splitCheckedCWith emit allowTC (SubC γ r1 r2)
        cs'' <- splitCheckedCWith emit allowTC (SubC γ r1' r2')
        cs''' <- splitCheckedCWith emit allowTC (SubC γ r2' r1')
        return $ cs ++ cs' ++ cs'' ++ cs'''
splitCheckedCWith emit allowTC (SubC γ t1 (RAllP p t)) =
    do
        name <- fresh
        let rigid = p{pname = name}
            renamed = mapScopedPredicate p (const (renamePredicate p rigid)) t
            t' = fmap (concretizePredicate rigid) renamed
        γ' <- addPToEnv γ rigid
        splitCheckedCWith (emit . (rigid :)) allowTC $ SubC γ' t1 t'
splitCheckedCWith emit allowTC (SubC γ (RAllP p t1) t2) =
    do
        r <- freshPredRef γ p
        let RProp formals (RHole replacement) = r
            substituted = substPredAtomicWith (\binder -> Just (binder, pname binder)) ordinarySpecType checkedLogical (\logical refinement -> refinement{checkedLogical = logical}) (\refinement logical -> meetCheckedRefinement refinement (CheckedRefinement logical [])) "splitC" p formals replacement t1
            replaced = mapScopedPredicate p (const (instantiatePredicateQueries p formals replacement)) substituted
        splitCheckedCWith emit allowTC $ SubC γ replaced t2
splitCheckedCWith emit allowTC (SubC γ t1'@(RAllT α1 t1 _) t2'@(RAllT α2 t2 _))
    | α1 == α2 =
        do
            γ' <- updateEnv γ α2
            cs <- emit [] γ t1' t2'
            cs' <- splitCheckedCWith emit allowTC $ SubC γ' t1 (substCheckedType su t2)
            return (cs ++ cs')
    | otherwise =
        do
            γ' <- updateEnv γ α2
            cs <- emit [] γ t1' t2'
            cs' <- splitCheckedCWith emit allowTC $ SubC γ' t1 (substCheckedType su t2'')
            return (cs ++ cs')
  where
    t2'' = substCheckedTyVar (ty_var_value α2, ty_var_value α1) t2
    su = case (rTVarToBind α1, rTVarToBind α2) of
        (Just (x1, _), Just (x2, _)) -> F.mkSubst [(x1, F.EVar x2)]
        _ -> F.mkSubst []

-- Primitive equality keeps its kind arguments, but its endpoints are invariant.
splitCheckedCWith emit _ (SubC γ (RApp c1 [_, _, l1, r1] _ _) (RApp c2 [_, _, l2, r2] _ _))
    | isEmbeddedDict c1 && c1 == c2 =
        splitsCWithVariance emit γ [l1, r1] [l2, r2] [Invariant, Invariant]
splitCheckedCWith emit _ (SubC γ t1@RApp{} t2@RApp{}) =
    do
        vv <- F.vv . Just <$> fresh
        let (t1', t2') = (shiftCheckedVV t1 vv, shiftCheckedVV t2 vv)
        cs <- emit [] γ t1' t2'
        γ' <- if bscope (getConfig γ) then γ `extendEnvWithVV` (ordinarySpecType t1') else return γ
        let RApp c t1s r1s _ = t1'
        let RApp _ t2s r2s _ = t2'
        let isapplied = True -- TC.tyConArity (rtc_tc c) == length t1s
        let tyInfo = rtc_info c
        csvar <- splitsCWithVariance emit γ' t1s t2s $ varianceTyArgs tyInfo
        csvar' <- rsplitsCWithVariance emit isapplied γ' r1s r2s $ variancePsArgs tyInfo
        return $ cs ++ csvar ++ csvar'
splitCheckedCWith emit _ (SubC γ t1@(RVar a1 _) t2@(RVar a2 _))
    | a1 == a2 =
        emit [] γ t1 t2
splitCheckedCWith _ _ (SubC _ (RLit l) (RLit l'))
    | l == l' =
        return []
splitCheckedCWith _ _ (SubC γ t1 t2) =
    panic (Just $ getLocation γ) $ "(Another Broken Test!!!) splitc unexpected:\n" ++ traceTy (ordinarySpecType t1) ++ "\n  <:\n" ++ traceTy (ordinarySpecType t2)
splitCheckedCWith _ _ (SubR γ o r) =
    do
        ts <- getTemplates
        let r1' = pruneUnsortedReft γ'' ts r1
        return $ F.subC γ' r1' r2 Nothing tag ci
  where
    γ'' = feEnv $ fenv γ
    γ' = feBinds $ fenv γ
    r1 = F.RR F.boolSort rr
    r2 = F.RR F.boolSort $ F.Reft (vv, F.EVar vv)
    vv = "vvRec"
    ci = Ci src (F.Delayed <$> err) (cgVar γ)
    err = Just $ ErrAssType src o (text $ show o ++ "type error") Nothing g (rHole rr)
    rr = toReft r
    tag = getTag γ
    src = getLocation γ
    g = reLocal $ renv γ

traceTy :: SpecType -> String
traceTy (RVar v _)      = parens ("RVar " ++ showpp v)
traceTy (RApp c ts _ _) = parens ("RApp " ++ showpp c ++ unwords (traceTy <$> ts))
traceTy (RAllP _ t)     = parens ("RAllP " ++ traceTy t)
traceTy (RAllT _ t _)   = parens ("RAllT " ++ traceTy t)
traceTy (RFun _ _ t t' _) = parens ("RFun " ++ parens (traceTy t) ++ parens (traceTy t'))
traceTy (REx _ tx t)    = parens ("REx " ++ parens (traceTy tx) ++ parens (traceTy t))
traceTy (RLit l)        = "RLit " ++ show l
traceTy (RExprArg _)    = "RExprArg"
traceTy (RAppTy t t' _) = parens ("RAppTy " ++ parens (traceTy t) ++ parens (traceTy t'))
traceTy (RHole _)       = "rHole"
traceTy (RRTy _ _ _ t)  = parens ("RRTy " ++ traceTy t)

parens :: String -> String
parens s = "(" ++ s ++ ")"

rHole :: F.Reft -> SpecType
rHole = RHole . uTop


splitsCWithVariance ::
    ([RPVar] -> CGEnv -> CheckedSpecType -> CheckedSpecType -> CG [FixSubC]) ->
    CGEnv ->
    [CheckedSpecType] ->
    [CheckedSpecType] ->
    [Variance] ->
    CG [FixSubC]
splitsCWithVariance emit γ t1s t2s variants =
    concatMapM (\(t1, t2, v) -> splitfWithVariance (\s1 s2 -> splitCheckedCWith emit (typeclass (getConfig γ)) (SubC γ s1 s2)) t1 t2 v) (zip3 t1s t2s variants)

rsplitsCWithVariance ::
    ([RPVar] -> CGEnv -> CheckedSpecType -> CheckedSpecType -> CG [FixSubC]) ->
    Bool ->
    CGEnv ->
    [RTProp RTyCon RTyVar CheckedRefinement] ->
    [RTProp RTyCon RTyVar CheckedRefinement] ->
    [Variance] ->
    CG [FixSubC]
rsplitsCWithVariance _ False _ _ _ _ =
    return []
rsplitsCWithVariance emit _ γ t1s t2s variants =
    concatMapM (\(t1, t2, v) -> splitfWithVariance (rsplitC emit γ) t1 t2 v) (zip3 t1s t2s variants)

bsplitC :: CGEnv
        -> SpecType
        -> SpecType
        -> CG [F.SubC Cinfo]
bsplitC γ t1 t2 = do
  temp   <- getTemplates
  isHO   <- gets allowHO
  t1'    <- addLhsInv γ <$> refreshVV t1
  return  $ bsplitC' γ t1' t2 temp isHO

addLhsInv :: CGEnv -> SpecType -> SpecType
addLhsInv γ t = addRTyConInv (invs γ) t `strengthen` r
  where
    r         = (mempty :: UReft) { ur_reft = F.Reft (F.dummySymbol, p) }
    p         = constraintToLogic rE' (lcs γ)
    rE'       = insertREnv v t (renv γ)
    v         = rTypeValueVar t


bsplitC' :: CGEnv -> SpecType -> SpecType -> F.Templates -> Bool -> [F.SubC Cinfo]
bsplitC' γ t1 t2 tem isHO
    | isHO =
        mkSubC γ' r1' r2' tag ci
    | F.isFunctionSortedReft r1' && F.isNonTrivial r2' =
        mkSubC γ' (r1'{F.sr_reft = mempty}) r2' tag ci
    | F.isNonTrivial r2' =
        mkSubC γ' r1' r2' tag ci
    | otherwise =
        []
  where
    γ' = feBinds $ fenv γ
    r1' = rTypeSortedReft' γ tem t1
    -- Inherited equation-deferral templates may weaken premises, but must
    -- never change the expected conclusion of the authored judgment.
    r2' = rTypeSortedReft (emb γ) t2
    tag = getTag γ
    src = getLocation γ
    g = reLocal $ renv γ

    ci sr = Ci src (F.Delayed <$> err sr) (cgVar γ)
    err sr = Just $ fromMaybe (ErrSubType src (text "subtype") Nothing g t1 (replaceTop t2 sr)) (cerr γ)

mkSubC :: F.IBindEnv -> F.SortedReft -> F.SortedReft -> F.Tag -> (F.SortedReft -> a) -> [F.SubC a]
mkSubC g sr1 sr2 tag ci = concatMap (\sr2' -> F.subC g sr1 sr2' Nothing tag (ci sr2')) (splitSortedReft sr2)

splitSortedReft :: F.SortedReft -> [F.SortedReft]
splitSortedReft (F.RR t (F.Reft (v, r))) = [ F.RR t (F.Reft (v, ra)) | ra <- refaConjuncts r ]

refaConjuncts :: F.Expr -> [F.Expr]
refaConjuncts p = [p' | p' <- F.conjuncts p, not $ F.isTautoPred p']

replaceTop :: SpecType -> F.SortedReft -> SpecType
replaceTop (RApp c ts rs r) r'  = RApp c ts rs $ replaceReft r r'
replaceTop (RVar a r) r'        = RVar a       $ replaceReft r r'
replaceTop (RFun b i t1 t2 r) r' = RFun b i t1 t2 $ replaceReft r r'
replaceTop (RAppTy t1 t2 r) r'  = RAppTy t1 t2 $ replaceReft r r'
replaceTop (RAllT a t r)    r'  = RAllT a t    $ replaceReft r r'
replaceTop t _                  = t

replaceReft :: RReft -> F.SortedReft -> RReft
replaceReft rr (F.RR _ r) = rr {ur_reft = F.Reft (v, F.subst1  p (vr, F.EVar v) )}
  where
    F.Reft (v, _)         = ur_reft rr
    F.Reft (vr,p)         = r

rsplitC :: ([RPVar] -> CGEnv -> CheckedSpecType -> CheckedSpecType -> CG [FixSubC])
        -> CGEnv
        -> RTProp RTyCon RTyVar CheckedRefinement
        -> RTProp RTyCon RTyVar CheckedRefinement
        -> CG [FixSubC]
rsplitC _ _ _ (RProp _ (RHole _))
  = panic Nothing "RefTypes.rsplitC on RProp _ (RHole _)"

rsplitC _ _ (RProp _ (RHole _)) _
  = panic Nothing "RefTypes.rsplitC on RProp _ (RHole _)"

rsplitC emit γ (RProp s1 r1) (RProp s2 r2)
  = do γ'  <-  foldM (+=) γ [("rsplitC1", x, ofRSort s) | (x, s) <- s2]
       splitCheckedCWith emit (typeclass (getConfig γ)) (SubC γ' (substCheckedType su r1) r2)
  where su = F.mkSubst [(x, F.EVar y) | ((x,_), (y,_)) <- zip s1 s2]


--------------------------------------------------------------------------------
-- | Reftypes from F.Fixpoint Expressions --------------------------------------
--------------------------------------------------------------------------------
forallExprRefType     :: CGEnv -> SpecType -> SpecType
forallExprRefType γ t = t `strengthen` uTop r'
  where
    r'                = fromMaybe mempty $ forallExprReft γ r
    r                 = F.sr_reft $ rTypeSortedReft (emb γ) t

forallExprReft :: CGEnv -> F.Reft -> Maybe F.Reft
forallExprReft γ r =
  do e <- F.isSingletonReft r
     forallExprReft_ γ $ F.splitEApp e

forallExprReft_ :: CGEnv -> (F.Expr, [F.Expr]) -> Maybe F.Reft
forallExprReft_ γ (F.EVar x, [])
  = case forallExprReftLookup γ x of
      Just (_,_,_,_,t)  -> Just $ F.sr_reft $ rTypeSortedReft (emb γ) t
      Nothing         -> Nothing

forallExprReft_ γ (F.EVar f, es)
  = case forallExprReftLookup γ f of
      Just (xs,_,_,_,t) -> let su = F.mkSubst $ safeZip "fExprRefType" xs es in
                       Just $ F.subst su $ F.sr_reft $ rTypeSortedReft (emb γ) t
      Nothing       -> Nothing

forallExprReft_ _ _
  = Nothing

-- forallExprReftLookup :: CGEnv -> F.Symbol -> Int
forallExprReftLookup :: CGEnv
                     -> F.Symbol
                     -> Maybe ([F.Symbol], [RFInfo], [SpecType], [RReft], SpecType)
forallExprReftLookup γ sym = snap <$> lookup' sym
  where
    snap     = mapFifth5 ignoreOblig . (\((x,a,b,c),t)->(x,a,b,c,t)) . bkArrow . thd3 . bkUniv
    lookup' z = γ ?= F.symbol z


--------------------------------------------------------------------------------
getTag :: CGEnv -> F.Tag
--------------------------------------------------------------------------------
getTag γ = maybe Tg.defaultTag (`Tg.getTag` tgEnv γ) (tgKey γ)


--------------------------------------------------------------------------------
-- | Constraint Generation Panic -----------------------------------------------
--------------------------------------------------------------------------------
panicUnbound :: (PPrint x) => CGEnv -> x -> a
panicUnbound γ x = Ex.throw (ErrUnbound (getLocation γ) (F.pprint x) :: Error)
