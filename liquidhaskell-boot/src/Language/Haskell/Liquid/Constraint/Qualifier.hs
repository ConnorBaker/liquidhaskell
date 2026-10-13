{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TypeOperators         #-}

module Language.Haskell.Liquid.Constraint.Qualifier
  ( giQuals
  , useSpcQuals
  )
  where

import           Prelude hiding (error)
import           Data.List                (partition)
import           Data.Maybe               (isJust, catMaybes, fromMaybe, isNothing)
import qualified Data.HashSet        as S
import qualified Data.HashMap.Strict as M
import           Debug.Trace (trace)
import           Control.Monad.Reader

import           Language.Fixpoint.Types                  hiding (panic, mkQual)
import qualified Language.Fixpoint.Types.Visitor as V
import qualified Language.Fixpoint.Types.Config as FC
import           Language.Fixpoint.Misc                  (fst3)
import           Language.Fixpoint.SortCheck
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.GHC.Misc         (getSourcePos)
import           Language.Haskell.Liquid.Misc             (condNull)
import           Language.Haskell.Liquid.Types.PredType
import           Liquid.GHC.API hiding (Expr, SrcSpan, mkQual, panic)

import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.Names (selfSymbol)
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.Specs
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.UX.Config
import           Language.Haskell.Liquid.Constraint.ToFixpoint (sourceNativeEnv)
import           Language.Fixpoint.Types.Config (ElabFlags)


--------------------------------------------------------------------------------
giQuals :: TargetInfo -> SEnv Sort -> [Qualifier]
--------------------------------------------------------------------------------
-- Declarations determine the ordered syntax inventory; the query determines
-- native applicability and whether each free symbol is a parameter or global.
giQuals info = interpret
  where
    signatures = signatureAtoms info
    aliases = aliasAtoms info
    interpret lEnv =
        notracepp ("GI-QUALS: " ++ showpp lEnv) $
            currentSpec
                ++ condNull (useSpcQuals info) otherSpecs
                ++ condNull (useSigQuals info) (sigQualifiers info signatures lEnv)
                ++ condNull (useAlsQuals info) (alsQualifiers info aliases lEnv)
    (currentSpec, otherSpecs) = partition isQualifierFromCurrentModule (gsQualifiers . gsQual . giSpec $ info)
    isQualifierFromCurrentModule qual =
        fst3 (sourcePosElts (qPos qual)) == giTarget (giSrc info)


-- --------------------------------------------------------------------------------
-- qualifiers :: GhcInfo -> SEnv Sort -> [Qualifier]
-- --------------------------------------------------------------------------------
-- qualifiers info env = spcQs ++ genQs
  -- where
    -- spcQs           = gsQualifiers spc
    -- genQs           = specificationQualifiers info env
    -- n               = maxParams (getConfig spc)
    -- spc             = spec info

maxQualParams :: (HasConfig t) => t -> Int
maxQualParams = maxParams . getConfig

-- | Use explicitly given qualifiers
useSpcQuals :: (HasConfig t) => t -> Bool
useSpcQuals i = useQuals i && not (useAlsQuals i)

-- | Scrape qualifiers from function signatures (incr :: x:Int -> {v:Int | v > x})
useSigQuals :: (HasConfig t) => t -> Bool
useSigQuals i = useQuals i && not (useAlsQuals i)

-- | Scrape qualifiers from refinement type aliases (type Nat = {v:Int | 0 <= 0})
useAlsQuals :: (HasConfig t) => t -> Bool
useAlsQuals i = useQuals i && i `hasOpt` higherOrderFlag && not (needQuals i)

useQuals :: (HasConfig t) => t -> Bool
useQuals = (FC.All /=) . eliminate . getConfig

needQuals :: (HasConfig t) => t -> Bool
needQuals = (FC.None == ) . eliminate . getConfig

--------------------------------------------------------------------------------
type QualifierAtoms = [(SourcePos, SEnv Sort, Symbol, Sort, Either [Expr] [Expr])]

aliasAtoms :: TargetInfo -> QualifierAtoms
aliasAtoms info =
    concat [refTypeAtoms tce emptySEnv (loc a) (rtBody (val a)) | a <- gsRTAliases (gsQual (giSpec info))]
  where
    tce = gsTcEmbeds (gsName (giSpec info))

alsQualifiers :: TargetInfo -> QualifierAtoms -> SEnv Sort -> [Qualifier]
alsQualifiers info atoms lEnv =
    [ q
    | q <- interpretAtoms native lEnv (elabFlag info) atoms
    , length (qParams q) <= maxQualParams info + 1
    , validQual native lEnv q
    ]
  where
    native = sourceNativeEnv (getConfig info) (gsADTs (gsName (giSpec info)))

elabFlag :: (HasConfig t) => t -> FC.ElabFlags
elabFlag info = FC.ElabFlags setBag False
  where
      setBag = maybe False elabSetBag . smtsolver . getConfig $ info
      elabSetBag :: FC.SMTSolver -> Bool
      elabSetBag FC.Z3    = True
      elabSetBag FC.Z3mem = True
      elabSetBag _        = False




validQual :: Maybe SymEnv -> SEnv Sort -> Qualifier -> Bool
validQual native lEnv q = isJust $ checkSortExpr native (srcSpan q) env (qBody q)
  where
    env          = unionSEnv lEnv qEnv
    qEnv         = M.fromList (qualBinds q)


--------------------------------------------------------------------------------
sigQualifiers :: TargetInfo -> QualifierAtoms -> SEnv Sort -> [Qualifier]
sigQualifiers info atoms lEnv =
    [q | q <- interpretAtoms native lEnv (elabFlag info) atoms, length (qParams q) <= maxQualParams info + 1]
  where
    native = sourceNativeEnv (getConfig info) (gsADTs (gsName (giSpec info)))

signatureAtoms :: TargetInfo -> QualifierAtoms
signatureAtoms info =
    [ atom
    | (x, t) <- specBinders info
    , not (x `S.member` S.fromList (specAxiomVars info))
    , atom <- refTypeAtoms tce (constructorScope x (val t)) (getSourcePos x) (val t)
    ]
  where
    tce = gsTcEmbeds (gsName (giSpec info))
    constructorOwners = S.fromList (map fst (gsCtors (gsData (giSpec info))))
    constructorScope x t
        | x `S.member` constructorOwners
        , (_, _, _, _, result@RApp{}) <- bkArrowDeep t =
            insertSEnv selfSymbol (rTypeSort tce result) emptySEnv
        | otherwise = emptySEnv

specBinders :: TargetInfo -> [(Var, LocSpecType)]
specBinders info = mconcat
  [ gsTySigs  (gsSig  sp)
  , gsAsmSigs (gsSig  sp)
  , gsRefSigs (gsSig  sp)
  , gsCtors   (gsData sp)
  , if info `hasOpt` scrapeInternals then gsInSigs (gsSig sp) else []
  ]
  where
    sp  = giSpec info

specAxiomVars :: TargetInfo -> [Var]
specAxiomVars =  gsReflects . gsRefl . giSpec

-- GRAVEYARD: scraping quals from imports kills the system with too much crap
-- specificationQualifiers info = {- filter okQual -} qs
--   where
--     qs                       = concatMap refTypeQualifiers ts
--     refTypeQualifiers        = refTypeQuals $ tcEmbeds spc
--     ts                       = val <$> t1s ++ t2s
--     t1s                      = [t | (x, t) <- tySigs spc, x `S.member` definedVars]
--     t2s                      = [] -- [t | (_, t) <- ctor spc                            ]
--     definedVars              = S.fromList $ defVars info
--     spc                      = spec info
--
-- okQual                       = not . any isPred . map snd . q_params
--   where
--     isPred (FApp tc _)       = tc == stringFTycon "Pred"
--     isPred _                 = False


-- TODO: rewrite using foldReft'
--------------------------------------------------------------------------------
refTypeAtoms :: TCEmb TyCon -> SEnv Sort -> SourcePos -> SpecType -> QualifierAtoms
--------------------------------------------------------------------------------
refTypeAtoms tce = scrapeType
  where
    scrapeType initialEnv l t0 = go [] initialEnv t0
      where
        scrape = refTopAtoms l tce
        add x t γ = insertSEnv x (rTypeSort tce t) γ
        goBind ps x t γ t' = go ps (add x t γ) t'
        go ps γ t@(RVar _ _) = scrape ps γ t
        go ps γ (RAllT _ t _) = go ps γ t
        go ps γ (RAllP p t) = go (p : ps) (insertSEnv (pname p) (rTypeSort tce (pvarRType p :: RSort)) γ) t
        go ps γ t@(RAppTy t1 t2 _) = go ps γ t1 ++ go ps γ t2 ++ scrape ps γ t
        go ps γ (RFun x _ t t' _) = go ps γ t ++ goBind ps x t γ t'
        go ps γ t@(RApp c ts rs _) = scrape ps γ t ++ concatMap (go ps γ') ts ++ goRefs ps c γ' rs
          where
            γ' = add (rTypeValueVar t) t γ
        go ps γ (REx x t t') = go ps γ t ++ goBind ps x t γ t'
        go _ _ _ = []
        goRefs ps c g rs = concat $ zipWith (goRef ps g) rs (rTyConPVs c)
        goRef _ _ (RProp _ (RHole _)) _ = []
        goRef ps g (RProp s t) _ = go ps (insertsSEnv' g s) t
        insertsSEnv' = foldr (\(x, t) γ -> insertSEnv x (rTypeSort tce t) γ)

refTopAtoms :: SourcePos -> TCEmb TyCon -> [RPVar] -> SEnv Sort -> SpecType -> QualifierAtoms
refTopAtoms l tce predicates γ rrt =
    [(l, γ, v, so, Left [pa | pa <- conjuncts ra, V.isConc pa])]
        ++ [ (l, insertSEnv v so γ, v, so, Right [PAtom Eq (EVar v) e])
           | let MkUReft _ (Pr ps) = fromMaybe (msg rrt) (stripRTypeBase rrt)
           , p <- findPVar predicates <$> ps
           , (s, _, e) <- pargs p
           , V.isConc e
           , let v = "vv"
                 so = rTypeSort tce s
           ]
  where
    RR so (Reft (v, ra)) = rTypeSortedReft tce rrt
    msg t = panic Nothing $ "Qualifier.refTopQuals: no typebase" ++ showpp t

interpretAtoms :: Maybe SymEnv -> SEnv Sort -> ElabFlags -> QualifierAtoms -> [Qualifier]
interpretAtoms native lEnv ef atoms =
    [ mkQual lEnv l () γ v so pa
    | (l, γ, v, so, observation) <- atoms
    , let contextHere = extendSortCheck (insertSEnv v so γ) context
    , pa <- either id id observation
    , case observation of
        Left _ ->
            notracepp ("refTopQuals: " ++ showpp pa) $
                isNothing (checkSortAt contextHere (srcSpan l) Nothing pa)
        Right _ -> True
    ]
  where
    context = runReader (prepareSortCheck native lEnv) ef

mkQual :: SEnv Sort
       -> SourcePos
       -> t
       -> SEnv Sort
       -> Symbol
       -> Sort
       -> Expr
       -> Qualifier
mkQual lEnv l _ γ v so p   = mkQ "Auto" ((v, so) : xts) p l
  where
    xs   = S.toList (S.delete v $ syms p)
    xts  = catMaybes $ zipWith (envSort l lEnv γ) xs [0..]

envSort :: SourcePos -> SEnv Sort -> SEnv Sort -> Symbol -> Integer -> Maybe (Symbol, Sort)
envSort l lEnv tEnv x i
  | Just t <- lookupSEnv x tEnv = Just (x, t)
  | Just _ <- lookupSEnv x lEnv = Nothing
  | otherwise                   = Just (x, ai)
  where
    ai             = trace msg $ fObj $ Loc l l $ tempSymbol "LHTV" i
    msg            = "Unknown symbol in qualifier: " ++ show x
