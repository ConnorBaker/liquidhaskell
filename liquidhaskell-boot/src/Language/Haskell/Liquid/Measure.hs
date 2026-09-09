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
  , dataConTypes
  , defRefType
  , bodyPred

  ) where

import           GHC                                    hiding (Located)
import           Prelude                                hiding (error)
import           Text.PrettyPrint.HughesPJ              hiding ((<>))
-- import           Data.Binary                            as B
-- import           GHC.Generics
import qualified Data.HashMap.Strict                    as M
import qualified Data.List                              as L
import qualified Data.Maybe                             as Mb -- (fromMaybe, isNothing)
import GHC.Stack

import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types                as F hiding (panic, R, DataDecl, SrcSpan, LocSymbol)
import           Liquid.GHC.API        as Ghc hiding (Expr, showPpr, panic, (<+>))
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types.RepMap
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


-- | Returns the specification types of all data constructors augmented with
-- the refinements from the measures. Also returns the specification types of
-- the measures in the second component of the result.
dataConTypes :: Bool -> F.TCEmb TyCon -> MSpec (RRType Reft) DataCon -> ([(Var, RRType Reft)], [(F.Located LHName, RRType Reft)])
dataConTypes allowTC embs s = (ctorTys, measTys)
  where
    measTys     = [(msName m, msSort m) | m <- M.elems (measMap s) ++ imeas s]
    ctorTys     = concatMap (makeDataConType allowTC embs . notracepp "HOHOH" . snd) (M.toList (ctorMap s))

makeDataConType :: Bool -> F.TCEmb TyCon -> [Def (RRType Reft) DataCon] -> [(Var, RRType Reft)]
makeDataConType _ _ []
  = []
makeDataConType allowTC _ ds | Mb.isNothing (dataConWrapId_maybe dc)
  = notracepp _msg [(woId, notracepp _msg $ combineDCTypes "cdc0" t ts)]
  where
    dc   = ctor (head ds)
    woId = dataConWorkId dc
    t    = varType woId
    ts   = defRefType allowTC t <$> ds
    _msg  = "makeDataConType0" ++ showpp (woId, t, ts)

makeDataConType allowTC embs ds
  = [(woId, noDummySyms woRType), (wrId, noDummySyms wrRType)]
  where
    -- A measure with missing argument types comes from a selector or checker
    -- measure. A measure with all the argument types available comes from a
    -- user definition.
    --
    -- BOTH kinds describe the wrapper, and withholding the selectors from it
    -- was harmless only while the wrapper and the worker took the same
    -- arguments. UNPACKing breaks that: from @-O1@ up GHC builds a record --
    -- @s { f = e }@ compiles to a construction -- through the WRAPPER, whose
    -- arguments are the SOURCE fields, which is exactly what a selector
    -- equation is written over. With the equations on the worker alone, a
    -- refinement naming a lifted selector is unprovable at every such site:
    -- the inferred type quotes @$WT ...@ while every @sel (T ...) == x@ fact
    -- in scope is about @T@. See 'tests/datacon/pos/UnpackedFieldUpdate.hs'.
    wr       = ds
    dc       = ctor $ head ds
    woId     = dataConWorkId dc
    wot      = varType woId
    wrId     = dataConWrapId dc
    wrt      = varType wrId
    -- A lifted measure equation is written over the constructor's SOURCE
    -- fields. That is also the WORKER's argument list -- unless GHC UNPACKed a
    -- strict field, from @-O1@ up, in which case the worker takes the
    -- components the field expanded to and the equation has to be rebuilt over
    -- them; 'toWorkerDef' does it over the constructor's 'RepMap'.
    --
    -- BOTH kinds need that rebuild, for the mirror image of the reason the
    -- wrapper needs both. A selector equation is written over the SOURCE
    -- fields just as a user equation is; the two differ only in whether the
    -- binders carry types, which 'toWorkerDef' does not consult -- it reads
    -- their names and 'dataConRepArgTys', and emits untyped binders itself.
    -- Rebuilding only the user ones left every @{-@ data @-}@-generated
    -- selector equation stated over source fields while the worker takes
    -- components, so 'stitchArgs' counted
    -- one binder against two arguments and rejected the declaration outright:
    -- @Requires 2 fields but given 1@. See
    -- 'tests/datacon/pos/UnpackedFieldBindersMulti.hs'.
    wots     = defRefType allowTC wot . toWorkerDef embs dc <$> ds
    wrts     = defRefType allowTC wrt <$> wr

    wrRType  = combineDCTypes "cdc1" wrt wrts
    woRType  = combineDCTypes "cdc2" wot wots

-- | Rewrite a measure equation from the constructor's source fields to the
-- WORKER's representation arguments. The identity unless GHC unpacked a strict
-- field, in which case each source binder is replaced by the reconstruction
-- of its field from the worker arguments it stands on: 'rebuildField' over
-- the constructor's 'RepMap', which is the one place that descent is decided.
--
-- The reconstruction is FLAT: a field expanded into a constructor @d'@ is
-- rebuilt as @d'@ applied to every leaf, with no intermediate constructor,
-- however deep the leaves were found. That is what the logic's @d'@ takes --
-- 'expandProductType' rewrites @d'@'s own spec the same way, so if GHC
-- unpacked a field of @d'@ the logic's @d'@ already takes that field's
-- components, and rebuilding the intermediate constructor would hand it a
-- value at the SOURCE field's sort (@Cannot unify (Array_t int bool) with
-- Keys@). The newtypes GHC unpacked THROUGH are the exception, because a
-- newtype has no worker and its logic symbol takes its one source field;
-- 'RepMap' records them and 'rebuildField' wraps them back on.
toWorkerDef :: F.TCEmb TyCon -> DataCon -> Def (RRType Reft) DataCon -> Def (RRType Reft) DataCon
toWorkerDef embs dc def@(Def f d mt xs body)
  | Right rm <- dataConRepMap embs dc
  , rmChanged rm
  , let repXs = [ F.tempSymbol (lhNameToResolvedSymbol (F.val f)) i
                | i <- [0 .. toInteger (sum (fieldLeafCount <$> rmFields rm)) - 1] ]
  , Just groups <- splitLeaves (rmFields rm) repXs
  , let es = zipWith rebuildField (rmFields rm) (map (map EVar) groups)
  , length es == length xs
  -- 'subst' is simultaneous, so it is safe for 'repXs' to reuse the names in
  -- 'xs': a binder introduced by the reconstruction is never itself rewritten.
  = Def f d mt [(x, Nothing) | x <- repXs] (subst (mkSubst (zip (fst <$> xs) es)) body)
  | otherwise
  = def

-- | If there are any dummy symbols in the type, replace them with fresh
-- variables.
--
-- Since 63ac730e5 this leans on 'subst' to do the renaming, and it renames
-- one binder fewer than the name suggests. 'mkSubst' drops every @(x, EVar x)@
-- pair, so @su@ is empty; 'subst' then reduces to @substr (syms t) mempty t@,
-- and 'syms' on an 'RType' DELETES bound binders, so 'dummySymbol' is not in
-- the initial scope set. 'freshInNS' hands the FIRST dummy binder back
-- unrenamed and inserts it, so the second and later ones collide and do get
-- fresh names.
--
-- Leaving the first one named 'dummySymbol' is load bearing: 'isDummy' is a
-- prefix test, but @Constraint.Env.(+=)@, @Types.Fresh.refreshRefType@ and
-- @Parse.hs@ each compare for exact equality with 'dummySymbol'.
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
defRefType :: Bool -> Type -> Def (RRType Reft) DataCon -> RRType Reft
defRefType allowTC tdc (Def f dc mt xs body)
                    = generalize $ mkArrow as' [] xts t'
  where
    xts             = stitchArgs allowTC (fSrcSpan f) dc xs ts
    t'              = refineWithCtorBody dc f body t
    t               = Mb.fromMaybe (ofType tr) mt
    (αs, ts, tr)    = splitType tdc
    as              = if Mb.isJust mt then [] else makeRTVar . rTyVar <$> αs
    as'             = map (, mempty) as

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
      isClassDc = Ghc.isClassTyCon (Ghc.dataConTyCon dc)
      -- For ordinary constructors, class dictionaries are constraint evidence,
      -- not fields. For class dictionary constructors, superclass dictionaries
      -- are fields and must be retained
      isErasable t
        | allowTC = isEmbeddedDictType t || (not isClassDc && Ghc.isClassPred t)
        | otherwise = Ghc.isSimplePredTy t

panicFieldNumMismatch :: (PPrint a, PPrint a1, PPrint a3)
                      => SrcSpan -> a3 -> a1 -> a -> a2
panicFieldNumMismatch sp dc nXs nTs  = panicDataCon sp dc msg
  where
    msg = "Requires" <+> pprint nTs <+> "fields but given" <+> pprint nXs

panicDataCon :: PPrint a1 => SrcSpan -> a1 -> Doc -> a
panicDataCon sp dc d
  = panicError $ ErrDataCon sp (pprint dc) d

refineWithCtorBody :: Outputable a
                   => a
                   -> F.Located LHName
                   -> Body
                   -> RType c tv Reft
                   -> RType c tv Reft
refineWithCtorBody dc f body t =
  case stripRTypeBase t of
    Just (Reft (v, _)) ->
      strengthen t $
        Reft (v, bodyPred (eApps (EVar $ lhNameToResolvedSymbol $ val f) [eVar v]) body)
    Nothing ->
      panic Nothing $ "measure mismatch " ++ showpp f ++ " on con " ++ showPpr dc


bodyPred ::  Expr -> Body -> Expr
bodyPred fv (E e)    = PAtom Eq fv e
bodyPred fv (P p)    = PIff  fv p
bodyPred fv (R v' p) = subst1 p (v', fv)
