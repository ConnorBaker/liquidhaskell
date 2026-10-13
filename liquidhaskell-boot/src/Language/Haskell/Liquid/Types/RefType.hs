{-# LANGUAGE IncoherentInstances       #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE TypeOperators             #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-} -- TODO(#1918): Only needed for GHC <9.0.1.
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-incomplete-record-updates #-}

-- | Refinement Types. Mostly mirroring the GHC Type definition, but with
--   room for refinements of various sorts.
-- TODO: Desperately needs re-organization.

module Language.Haskell.Liquid.Types.RefType (

    TyConMap

  -- * Functions for lifting Reft-values to Spec-values
  , uTop, uReft, uRType, uRType', uRTypeGen, uPVar
  , specTypeToQueryType

  -- * Applying a solution to a SpecType
  , applySolution

  -- * Functions for decreasing arguments
  , isDecreasing, makeNumEnv, mkDecrFun
  , makeLexRefa

  -- * Functions for manipulating `Predicate`s
  , pdVar
  , findPVar
  , FreeVar, allTyVars, allTyVars', freeTyVars, tyClasses, tyConName

  -- * Quantifying RTypes
  , quantifyRTy
  , quantifyFreeRTy

  -- * RType constructors
  , ofType, toType, bareOfType
  , bTyVar, rTyVar, rVar, rApp, gApp, rEx
  , symbolRTyVar, bareRTyVar
  , tyConBTyCon
  , pdVarReft

  -- * Substitutions
  , subts, subvPredicate, subvUReft
  , subsTyVarMeet, subsTyVarMeet', subsTyVarMeetWith, subsTyVarNoMeet
  , subsFreeWith
  , subsTyVarsNoMeet, subsTyVarsMeet

  -- * Destructors
  , addTyConInfo
  , appRTyCon
  , typeUniqueSymbol
  , classBinds
  , isSizeable
  , famInstTyConType
  , famInstArgs

  -- * Manipulating Refinements in RTypes
  , strengthen
  , strengthenWith
  , generalize
  , normalizePds
  , dataConMsReft
  , dataConReft
  , rTypeSortedReft
  , rTypeSort
  , typeSort
  , interpretEmbeddingSort
  , interpretEmbedding
  , newtypeIdentitySort
  , shiftVV
  , shiftVVWith

  -- * TODO: classify these
  -- , mkDataConIdsTy
  , expandProductType
  , mkTyConInfo
  , strengthenRefTypeGen
  , strengthenDataConType
  , isBaseTy
  , updateRTVar, isValKind, kindToRType
  , rTVarInfo

  , tyVarsPosition, Positions(..)

  , isNumeric

  ) where

-- import           GHC.Stack
import Prelude hiding (error)
-- import qualified Prelude
import           Data.Maybe               (fromMaybe, isJust)
import           Data.Monoid              (First(..))
import           Data.Hashable
import qualified Data.HashMap.Strict  as M
import qualified Data.HashSet         as S
import qualified Data.List as L
import           Text.Printf
import           Text.PrettyPrint.HughesPJ hiding ((<>), first)
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types hiding (DataDecl (..), DataCtor (..), panic, shiftVV, Predicate, isNumeric, trueReft)
import           Language.Fixpoint.Types.Visitor (trans, Visitable)
import qualified Language.Fixpoint.Types.Visitor as FV
import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.PrettyPrint

import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Variance
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.Types.Names
import qualified Language.Haskell.Liquid.GHC.Misc as GM
import           Liquid.GHC.API        as Ghc hiding ( Expr, get
                                                                      , Located
                                                                      , tyConName
                                                                      , punctuate
                                                                      , hcat
                                                                      , (<+>)
                                                                      , parens
                                                                      , empty
                                                                      , dcolon
                                                                      , vcat
                                                                      , nest
                                                                      , ($+$)
                                                                      , panic
                                                                      , text
                                                                      )
import           Language.Haskell.Liquid.GHC.TypeRep () -- Eq Type instance
import           GHC.Core.DataCon (dataConOrigResTy)
import           GHC.Core.Type (coreView, typeKind)
import qualified GHC.Core.Type as Ghc (mkAppTy, mkInvisFunTy, mkSpecForAllTy, mkVisFunTyMany)







strengthenDataConType :: (Var, SpecType) -> (Var, SpecType)
strengthenDataConType (x, t) = (x, fromRTypeRep trep {ty_res = tres})
  where
    tres     = F.notracepp _msg $ ty_res trep `strengthen` MkUReft (exprReft expr') mempty
    trep     = toRTypeRep t
    _msg     = "STRENGTHEN-DATACONTYPE x = " ++ F.showpp (x, zip xs ts)
    (xs, ts) = dataConArgs trep
    as       = ty_vars  trep
    x'       = symbol x
    expr' :: Expr
    expr' | null xs && null as = EVar x'
          | otherwise          = mkEApp (dummyLoc x') (EVar <$> xs)


dataConArgs :: SpecRep -> ([Symbol], [SpecType])
dataConArgs trep = unzip [ (x, t) | (x, t) <- zip xs ts, isValTy t]
  where
    xs           = ty_binds trep
    ts           = ty_args trep
    isValTy      = not . GM.isEmbeddedDictType . toType False


pdVar :: PVarV v t -> PredicateV v
pdVar v  = Pr [uPVar v]

findPVar :: [PVar (RType c tv NoReft)] -> UsedPVar -> PVar (RType c tv NoReft)
findPVar ps upv = PV name ty (zipWith (\(_, _, e) (t, s, _) -> (t, s, e)) (pargs upv) args)
  where
    PV name ty args = fromMaybe (msg upv) $ L.find ((== pname upv) . pname) ps
    msg p = panic Nothing $ "RefType.findPVar" ++ showpp p ++ "not found"

-- | Various functions for converting vanilla `Reft` to `Spec`

uRType          ::  RType c tv Reft -> RType c tv UReft
uRType          = fmap uTop

uRType'         ::  RType c tv UReft -> RType c tv Reft
uRType'         = fmap ur_reft

uRTypeGen       :: IsReft b => RType c tv a -> RType c tv b
uRTypeGen       = fmap $ const trueReft

uPVar           :: PVarV v t -> UsedPVarV v
uPVar           = fmap (const NoReft)

uReft           :: (Symbol, Expr) -> UReft
uReft           = uTop . Reft

uTop            :: ReftV v -> UReftV v
uTop r          = MkUReft r (Pr [])

--------------------------------------------------------------------
-------------- (Class) Predicates for Valid Refinement Types -------
--------------------------------------------------------------------


-- Monoid Instances ---------------------------------------------------------

instance ( SubsTy tv (RTypeBV v v c tv (NoReftB v)) (RTypeBV v v c tv (NoReftB v))
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) c
         , OkRTBV v v c tv r
         , FreeVar c tv
         , Subable r
         , F.Variable r ~ v
         , ReftBind r ~ v
         , ReftVar r ~ v
         , IsReft r
         , Meet r
         , F.Refreshable v
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) r
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) Sort
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) tv
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) (RTVar v v c tv)
         )
        => Semigroup (RTypeBV v v c tv r)  where
  (<>) = strengthenRefType

-- TODO: remove, use only Semigroup?
instance ( SubsTy tv (RTypeBV v v c tv (NoReftB v)) (RTypeBV v v c tv (NoReftB v))
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) c
         , OkRTBV v v c tv r
         , FreeVar c tv
         , Subable r
         , F.Variable r ~ v
         , ReftBind r ~ v
         , ReftVar r ~ v
         , IsReft r
         , Meet r
         , F.Refreshable v
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) r
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) Sort
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) tv
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) (RTVar v v c tv)
         )
        => Monoid (RTypeBV v v c tv r)  where
  mempty  = panic Nothing "mempty: RType"

-- MOVE TO TYPES
instance ( SubsTy tv (RTypeBV v v c tv (NoReftB v)) c
         , OkRTBV v v c tv r
         , Variable r ~ v
         , ReftBind r ~ v
         , ReftVar r ~ v
         , IsReft r
         , Meet r
         , FreeVar c tv
         , Subable r
         , F.Refreshable v
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) r
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) Sort
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) (RTypeBV v v c tv (NoReftB v))
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) tv
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) (RTVar v v c tv)
         )
         => Semigroup (RTPropBV v v c tv r) where
  (<>) (RProp s1 (RHole r1)) (RProp s2 (RHole r2))
    | isTauto r1 = RProp s2 (RHole r2)
    | isTauto r2 = RProp s1 (RHole r1)
    | otherwise  = RProp s1 $ RHole $ r1 `meet`
                               subst (mkSubst $ zip (fst <$> s2) (EVar . fst <$> s1)) r2

  (<>) (RProp s1 t1) (RProp s2 t2)
    | isTrivial t1 = RProp s2 t2
    | isTrivial t2 = RProp s1 t1
    | otherwise    = RProp s1 $ t1  `strengthenRefType`
                                subst (mkSubst $ zip (fst <$> s2) (EVar . fst <$> s1)) t2

instance ( SubsTy tv (RTypeBV v v c tv (NoReftB v)) c
         , OkRTBV v v c tv r
         , Variable r ~ v
         , ReftBind r ~ v
         , ReftVar r ~ v
         , IsReft r
         , Meet r
         , FreeVar c tv
         , Subable r
         , F.Refreshable v
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) r
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) Sort
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) (RTypeBV v v c tv (NoReftB v))
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) tv
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) (RTVar v v c tv)
         )
         => Meet (RTPropBV v v c tv r) where

-- TODO: remove and use only Semigroup?
instance ( SubsTy tv (RTypeBV v v c tv (NoReftB v)) c
         , OkRTBV v v c tv r
         , Variable r ~ v
         , ReftBind r ~ v
         , ReftVar r ~ v
         , IsReft r
         , Meet r
         , FreeVar c tv
         , Subable r
         , F.Refreshable v
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) r
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) Sort
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) (RTypeBV v v c tv (NoReftB v))
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) tv
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) (RTVar v v c tv)
         )
         => Monoid (RTPropBV v v c tv r) where
  mempty  = panic Nothing "mempty: RTProp"
  mappend = (<>)

instance Semigroup (RType RTyCon RTyVar r) => Meet (RType RTyCon RTyVar r) where

-- MOVE TO TYPES
instance Fixpoint String where
  toFix = text

-- MOVE TO TYPES
instance Fixpoint Class where
  toFix = text . GM.showPpr

-- MOVE TO TYPES
class FreeVar a v where
  freeVars :: a -> [v]

-- MOVE TO TYPES
instance FreeVar RTyCon RTyVar where
  freeVars = (RTV <$>) . GM.tyConTyVarsDef . rtc_tc

-- MOVE TO TYPES
instance FreeVar BTyCon BTyVar where
  freeVars _ = []

-- Eq Instances ------------------------------------------------------

-- MOVE TO TYPES
instance (Eq c, Eq tv, Hashable tv, PPrint tv, TyConable c, PPrint c)
      => Eq (RType c tv NoReft) where
  (==) = eqRSort M.empty

eqRSort :: (Eq a, Eq k, Hashable k, TyConable a, PPrint a, PPrint k)
        => M.HashMap k k -> RType a k NoReft -> RType a k NoReft -> Bool
eqRSort m (RAllP _ t) (RAllP _ t')
  = eqRSort m t t'
eqRSort m (RAllP _ t) t'
  = eqRSort m t t'
eqRSort m (RAllT a t _) (RAllT a' t' _)
  | a == a'
  = eqRSort m t t'
  | otherwise
  = eqRSort (M.insert (ty_var_value a') (ty_var_value a) m) t t'
eqRSort m (RAllT _ t _) t'
  = eqRSort m t t'
eqRSort m t (RAllT _ t' _)
  = eqRSort m t t'
eqRSort m (RFun _ _ t1 t2 _) (RFun _ _ t1' t2' _)
  = eqRSort m t1 t1' && eqRSort m t2 t2'
eqRSort m (RAppTy t1 t2 _) (RAppTy t1' t2' _)
  = eqRSort m t1 t1' && eqRSort m t2 t2'
eqRSort m (RApp c ts _ _) (RApp c' ts' _ _)
  = c == c' && length ts == length ts' && and (zipWith (eqRSort m) ts ts')
eqRSort m (RVar a _) (RVar a' _)
  = a == M.lookupDefault a' a' m
eqRSort _ (RLit l) (RLit l')
  = l == l'
eqRSort _ (RHole _) _
  = True
eqRSort _ _         (RHole _)
  = True
eqRSort _ _ _
  = False

--------------------------------------------------------------------------------
-- | Wrappers for GHC Type Elements --------------------------------------------
--------------------------------------------------------------------------------

instance Eq RTyVar where
  -- FIXME: need to compare unique and string because we reuse
  -- uniques in stringTyVar and co.
  RTV α == RTV α' = α == α' && getOccName α == getOccName α'

instance Ord RTyVar where
  compare (RTV α) (RTV α') = case compare α α' of
    EQ -> compare (getOccName α) (getOccName α')
    o  -> o

instance Hashable RTyVar where
  hashWithSalt i (RTV α) = hashWithSalt i α

-- TyCon isn't comparable
--instance Ord RTyCon where
--  compare x y = compare (rtc_tc x) (rtc_tc y)

instance Hashable RTyCon where
  hashWithSalt i = hashWithSalt i . rtc_tc

--------------------------------------------------------------------------------
-- | Helper Functions (RJ: Helping to do what?) --------------------------------
--------------------------------------------------------------------------------

rVar :: IsReft r => TyVar -> RType c RTyVar r
rVar   = (`RVar` trueReft) . RTV

rTyVar :: TyVar -> RTyVar
rTyVar = RTV

-- | Compute 'RTVarInfo' for an 'RTVar' if the info is not already present.
updateRTVar :: SpecRTVar -> SpecRTVar
updateRTVar (RTVar (RTV a) RTVNoInfo{}) = RTVar (RTV a) (rTVarInfo a)
updateRTVar v = v

rTVar :: TyVar -> RTVar Symbol Symbol RTyCon RTyVar
rTVar a = RTVar (RTV a) (rTVarInfo a)

bTVar :: TyVar -> RTVar Symbol Symbol BTyCon BTyVar
bTVar a = RTVar (BTV (symbol <$> GM.locNamedThing a)) (bTVarInfo a)

bTVarInfo :: TyVar -> RTVInfo Symbol Symbol BTyCon BTyVar
bTVarInfo = mkTVarInfo kindToBRType

rTVarInfo :: TyVar -> RTVInfo Symbol Symbol RTyCon RTyVar
rTVarInfo = mkTVarInfo kindToRType

mkTVarInfo :: (Kind -> RTypeBV Symbol v c tv (NoReftBV Symbol v)) -> TyVar -> RTVInfo Symbol v c tv
mkTVarInfo k2t a = RTVInfo
  { rtv_name   = symbol    $ varName a
  , rtv_kind   = k2t       $ tyVarKind a
  , rtv_is_val = isValKind $ tyVarKind a
  , rtv_is_pol = True
  }

kindToRType :: IsReft r => Type -> RRType r
kindToRType = kindToRType_ ofType

kindToBRType :: IsReft r => Type -> BRType r
kindToBRType = kindToRType_ bareOfType

kindToRType_ :: (Type -> z) -> Type -> z
kindToRType_ ofType'       = ofType' . go
  where
    go t
     | t == typeSymbolKind = stringTy
     | t == naturalTy      = intTy
     | otherwise           = t

isValKind :: Kind -> Bool
isValKind x0 =
    let x = expandTypeSynonyms x0
     in x == naturalTy || x == typeSymbolKind

bTyVar :: LocSymbol -> BTyVar
bTyVar      = BTV

symbolRTyVar :: Symbol -> RTyVar
symbolRTyVar = rTyVar . GM.symbolTyVar

bareRTyVar :: BTyVar -> RTyVar
bareRTyVar (BTV tv) = symbolRTyVar $ val tv

normalizePds :: (OkRT c tv r) => RType c tv r -> RType c tv r
normalizePds t = addPds ps t'
  where
    (t', ps)   = nlzP [] t

rPred :: PVar (RType c tv NoReft) -> RType c tv r -> RType c tv r
rPred     = RAllP

rEx :: Foldable t
    => t (Symbol, RType c tv r) -> RType c tv r -> RType c tv r
rEx xts rt = foldr (\(x, tx) t -> REx x tx t) rt xts

rApp :: TyCon
     -> [RType RTyCon tv r]
     -> [RTProp RTyCon tv r]
     -> r
     -> RType RTyCon tv r
rApp c = RApp (tyConRTyCon c)

gApp :: TyCon -> [RTyVar] -> [PVar a] -> SpecType
gApp tc αs πs = rApp tc
                  [rVar α | RTV α <- αs]
                  (rPropP [] . pdVarReft <$> πs)
                  mempty

pdVarReft :: PVar t -> UReft
pdVarReft = (\p -> MkUReft mempty p) . pdVar

tyConRTyCon :: TyCon -> RTyCon
tyConRTyCon c = RTyCon c [] (mkTyConInfo c [] [] Nothing)

-- bApp :: (Monoid r) => TyCon -> [BRType r] -> BRType r
bApp :: TyCon -> [BRType r] -> [BRProp r] -> r -> BRType r
bApp c = RApp (tyConBTyCon c)

tyConBTyCon :: TyCon -> BTyCon
tyConBTyCon tc =
  mkBTyCon $
    makeResolvedLHName (LHRGHC (getName tc)) . tyConName <$> GM.locNamedThing tc


--- NV TODO : remove this code!!!

addPds :: Foldable t
       => t (PVar (RType c tv NoReft)) -> RType c tv r -> RType c tv r
addPds ps (RAllT v t r) = RAllT v (addPds ps t) r
addPds ps t             = foldl' (flip rPred) t ps

nlzP :: (OkRT c tv r) => [PVar (RType c tv NoReft)] -> RType c tv r -> (RType c tv r, [PVar (RType c tv NoReft)])
nlzP ps t@(RVar _ _ )
 = (t, ps)
nlzP ps t@(RLit _)
 = (t, ps)
nlzP ps (RFun b i t1 t2 r)
 = (RFun b i t1' t2' r, ps ++ ps1 ++ ps2)
  where (t1', ps1) = nlzP [] t1
        (t2', ps2) = nlzP [] t2
nlzP ps (RAppTy t1 t2 r)
 = (RAppTy t1' t2' r, ps ++ ps1 ++ ps2)
  where (t1', ps1) = nlzP [] t1
        (t2', ps2) = nlzP [] t2
nlzP ps (RAllT v t r)
 = (RAllT v t' r, ps ++ ps')
  where (t', ps') = nlzP [] t
nlzP ps t@RApp{}
 = (t, ps)
nlzP ps (RAllP p t)
 = (t', [p] ++ ps ++ ps')
  where (t', ps') = nlzP [] t
nlzP ps t@REx{}
 = (t, ps)
nlzP ps t@(RRTy _ _ _ t')
 = (t, ps ++ ps')
 where ps' = snd $ nlzP [] t'
nlzP _ t
 = panic Nothing $ "RefType.nlzP: cannot handle " ++ F.showpp t

strengthenRefTypeGen, strengthenRefType ::
         ( OkRTBV v v c tv r
         , Subable r
         , F.Variable r ~ v
         , ReftBind r ~ v
         , ReftVar r ~ v
         , IsReft r
         , Meet r
         , F.Refreshable v
         , FreeVar c tv
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) (RTypeBV v v c tv (NoReftB v))
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) c
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) r
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) Sort
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) tv
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) (RTVar v v c tv)
         ) => RTypeBV v v c tv r -> RTypeBV v v c tv r -> RTypeBV v v c tv r

strengthenRefType_ ::
         ( OkRTBV v v c tv r
         , Subable r
         , F.Variable r ~ v
         , ReftBind r ~ v
         , ReftVar r ~ v
         , IsReft r
         , Meet r
         , F.Refreshable v
         , FreeVar c tv
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) (RTypeBV v v c tv (NoReftB v))
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) c
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) r
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) Sort
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) (RTVar v v c tv)
         , SubsTy tv (RTypeBV v v c tv (NoReftB v)) tv
         ) => (RTypeBV v v c tv r -> RTypeBV v v c tv r -> RTypeBV v v c tv r)
           ->  RTypeBV v v c tv r -> RTypeBV v v c tv r -> RTypeBV v v c tv r

strengthenRefTypeGen = strengthenRefType_ f
  where
    f :: (OkRTBV v v c tv r, IsReft r, Meet r) => RTypeBV v v c tv r -> RTypeBV v v c tv r -> RTypeBV v v c tv r
    f (RVar v1 r1) t  = RVar v1 (r1 `meet` fromMaybe trueReft (stripRTypeBase t))
    f t (RVar _ r1)  = t `strengthen` r1
    f t1 t2           = panic Nothing $ printf "strengthenRefTypeGen on differently shaped types \nt1 = %s [shape = %s]\nt2 = %s [shape = %s]"
                         (pprRaw t1) (showpp (toRSort t1)) (pprRaw t2) (showpp (toRSort t2))

pprRaw :: (OkRTBV b v c tv r) => RTypeBV b v c tv r -> String
pprRaw = render . rtypeDoc Full

{- [NOTE:StrengthenRefType] disabling the `meetable` check because

      (1) It requires the 'TCEmb TyCon' to deal with the fact that sometimes,
          GHC uses the "Family Instance" TyCon e.g. 'R:UniquePerson' and sometimes
          the vanilla TyCon App form, e.g. 'Unique Person'
      (2) We could pass in the TCEmb but that would break the 'Monoid' instance for
          RType. The 'Monoid' instance was was probably a bad idea to begin with,
          and we probably ought to do away with it entirely, but thats a battle I'll
          leave for another day.

    Consequently, its up to users of `strengthenRefType` (and associated functions)
    to make sure that the two types are compatible. For an example, see 'meetVarTypes'.
 -}

strengthenRefType t1 t2
  -- | _meetable t1 t2
  = strengthenRefType_ const t1 t2
  -- | otherwise
  -- = panic Nothing msg
  -- where
  --   msg = printf "strengthen on differently shaped reftypes \nt1 = %s [shape = %s]\nt2 = %s [shape = %s]"
  --           (showpp t1) (showpp (toRSort t1)) (showpp t2) (showpp (toRSort t2))

_meetable :: (OkRTBV b v c tv r) => RTypeBV b v c tv r -> RTypeBV b v c tv r -> Bool
_meetable t1 t2 = toRSort t1 == toRSort t2

strengthenRefType_ f (RAllT a1 t1 r1) (RAllT a2 t2 r2)
  = RAllT a1 (strengthenRefType_ f t1 (subsTyVarMeet (ty_var_value a2, toRSort t, t) t2)) (r1 `meet` r2)
  where t = RVar (ty_var_value a1) trueReft

strengthenRefType_ f (RAllT a t1 r1) t2
  = RAllT a (strengthenRefType_ f t1 t2) r1

strengthenRefType_ f t1 (RAllT a t2 r2)
  = RAllT a (strengthenRefType_ f t1 t2) r2

strengthenRefType_ f (RAllP p1 t1) (RAllP _ t2)
  = RAllP p1 $ strengthenRefType_ f t1 t2

strengthenRefType_ f (RAllP p t1) t2
  = RAllP p $ strengthenRefType_ f t1 t2

strengthenRefType_ f t1 (RAllP p t2)
  = RAllP p $ strengthenRefType_ f t1 t2

strengthenRefType_ f (RAppTy t1 t1' r1) (RAppTy t2 t2' r2)
  = RAppTy t t' (r1 `meet` r2)
    where t  = strengthenRefType_ f t1 t2
          t' = strengthenRefType_ f t1' t2'

strengthenRefType_ f (RFun x1 i1 t1 t1' r1) (RFun x2 i2 t2 t2' r2) =
  -- YL: Evidence that we need a Monoid instance for RFInfo?
  if x2 /= F.wildcard
    then RFun x2 i1{permitTC = getFirst b} t t1'' (r1 `meet` r2)
    else RFun x1 i1{permitTC = getFirst b} t t2'' (r1 `meet` r2)
    where t  = strengthenRefType_ f t1 t2
          t1'' = strengthenRefType_ f (subst1 t1' (x1, EVar x2)) t2'
          t2'' = strengthenRefType_ f t1' (subst1 t2' (x2, EVar x1))
          b  = First (permitTC i1) <> First (permitTC i2)

strengthenRefType_ f (RApp tid t1s rs1 r1) (RApp _ t2s rs2 r2)
  = RApp tid ts rs (r1 `meet` r2)
    where ts  = zipWith (strengthenRefType_ f) t1s t2s
          rs  = meets rs1 rs2

strengthenRefType_ _ (RVar v1 r1)  (RVar v2 r2) | v1 == v2
  = RVar v1 (r1 `meet` r2)
strengthenRefType_ _ t1@(RLit l) t2@(RLit l')
  | l == l' = t1
  | otherwise = panic Nothing $ "Cannot strengthen distinct type literals: " ++ showpp t1 ++ " and " ++ showpp t2
strengthenRefType_ f t1 t2
  = f t1 t2

meets :: (Meet r) => [r] -> [r] -> [r]
meets [] rs                 = rs
meets rs []                 = rs
meets rs rs'
  | length rs == length rs' = zipWith meet rs rs'
  | otherwise               = panic Nothing "meets: unbalanced rs"

strengthen :: (Meet r, IsReft r, Eq (ReftVar r)) => RTypeBV b v c tv r -> r -> RTypeBV b v c tv r
strengthen = strengthenWith meet

strengthenWith :: (IsReft r, Eq (ReftVar r)) => (r -> r -> r) -> RTypeBV b v c tv r -> r -> RTypeBV b v c tv r
strengthenWith = strengthenWithTest isTauto

strengthenWithTest :: (r -> Bool) -> (r -> r -> r) -> RTypeBV b v c tv r -> r -> RTypeBV b v c tv r
strengthenWithTest trivial mt = go
  where
    go (RApp c ts rs r) r' = RApp c ts rs (r `mt` r')
    go (RVar a r) r' = RVar a (r `mt` r')
    go (RFun b i t1 t2 r) r' = RFun b i t1 t2 (r `mt` r')
    go (RAppTy t1 t2 r) r' = RAppTy t1 t2 (r `mt` r')
    go (RAllT a t r) r' = RAllT a t (r `mt` r')
    go (RHole r) r' = RHole (r `mt` r')
    go t@(RLit _) r
        | trivial r = t
        | otherwise = panic Nothing "A type-level literal cannot carry a value refinement"
    go t _ = t


quantifyRTy :: (Monoid r, Eq tv) => [RTVar Symbol v c tv] -> RTypeV v c tv r -> RTypeV v c tv r
quantifyRTy tvs ty = foldr rAllT ty tvs
  where rAllT a t = RAllT a t mempty

quantifyFreeRTy :: (Monoid r, Eq tv) => RTypeV v c tv r -> RTypeV v c tv r
quantifyFreeRTy ty = quantifyRTy (freeTyVars ty) ty


-------------------------------------------------------------------------
addTyConInfo :: (PPrint r, IsReft r, SubsTy RTyVar RSort r, Variable r ~ Symbol, ReftBind r ~ Symbol, ReftVar r ~ Symbol, IsReft r, Meet r)
             => TCEmb TyCon
             -> TyConMap
             -> RRType r
             -> RRType r
-------------------------------------------------------------------------
addTyConInfo tce tyi = mapBot (expandRApp tce tyi)

-------------------------------------------------------------------------
expandRApp :: (PPrint r, IsReft r, SubsTy RTyVar RSort r, Variable r ~ Symbol, ReftBind r ~ Symbol, ReftVar r ~ Symbol, IsReft r, Meet r)
           => TCEmb TyCon -> TyConMap -> RRType r -> RRType r
-------------------------------------------------------------------------
expandRApp tce tyi t@RApp{} = RApp rc' ts rs' r
  where
    RApp rc ts rs r            = t
    (rc', _)                   = appRTyCon tce tyi rc as
    pvs                        = rTyConPVs rc'
    rs'                        = applyNonNull rs0 (rtPropPV rc pvs) rs
    rs0                        = rtPropTop <$> pvs
    n                          = length fVs
    fVs                        = GM.tyConTyVarsDef $ rtc_tc rc
    as                         = choosen n ts (rVar <$> fVs)
expandRApp _ _ t               = t

choosen :: Int -> [a] -> [a] -> [a]
choosen 0 _ _           = []
choosen i (x:xs) (_:ys) = x:choosen (i-1) xs ys
choosen i []     (y:ys) = y:choosen (i-1) [] ys
choosen _ _ _           = impossible Nothing "choosen: this cannot happen"


rtPropTop
  :: (OkRT c tv r,
      IsReft r,
      SubsTy tv (RType c tv NoReft) c, SubsTy tv (RType c tv NoReft) r, SubsTy tv (RType c tv NoReft) Sort,
      SubsTy tv (RType c tv NoReft) (RType c tv NoReft), FreeVar c tv,
      SubsTy tv (RType c tv NoReft) tv,
      SubsTy tv (RType c tv NoReft) (RTVar Symbol Symbol c tv))
   => PVar (RType c tv NoReft) -> Ref (RType c tv NoReft) (RType c tv r)
rtPropTop pv = RProp (pvArgs pv) $ ofRSort $ ptype pv

rtPropPV :: (Fixpoint a, IsReft r, Meet r, Eq (ReftVar r))
         => a
         -> [PVar (RType c tv NoReft)]
         -> [Ref (RType c tv NoReft) (RType c tv r)]
         -> [Ref (RType c tv NoReft) (RType c tv r)]
rtPropPV _rc = zipWith mkRTProp

-- | Eliminates top-level RHoles. See @goRProps@ inside 'goPlugged' in
-- Plugged.hs for the handling of nested RHoles.
mkRTProp :: (IsReft r, Meet r, Eq (ReftVar r))
         => PVar (RType c tv NoReft)
         -> Ref (RType c tv NoReft) (RType c tv r)
         -> Ref (RType c tv NoReft) (RType c tv r)
mkRTProp pv (RProp ss (RHole r))
  = RProp ss $ ofRSort (pvType pv) `strengthen` r

mkRTProp pv (RProp ss t)
  | length (pargs pv) == length ss
  = RProp ss t
  | otherwise
  = RProp (pvArgs pv) t

pvArgs :: PVar t -> [(Symbol, t)]
pvArgs pv = [(s, t) | (t, s, _) <- pargs pv]

{- | [NOTE:FamInstPredVars] related to [NOTE:FamInstEmbeds]
     See tests/datacon/pos/T1446.hs
     The function txRefSort converts

        Int<p>              ===> {v:Int | p v}

     which is fine, but also converts

        Field<q> Blob a     ===> {v:Field Blob a | q v}

     which is NOT ok, because q expects a different arg.

     The above happens because, thanks to instance-family stuff,
     LH doesn't realize that q is actually an ARG of Field Blob
     Note that Field itself has no args, but Field Blob does...

     That is, it is not enough to store the refined `TyCon` info,
     solely in the `RTyCon` as with family instances, you need BOTH
     the `TyCon` and the args to determine the extra info.

     We do so in `TyConMap`, and by crucially extending

     @RefType.appRTyCon@ whose job is to use the Refined @TyCon@
     that is, the @RTyCon@ generated from the @TyConP@ to strengthen
     individual occurrences of the TyCon applied to various arguments.

 -}

appRTyCon :: (ToTypeable r) => TCEmb TyCon -> TyConMap -> RTyCon -> [RRType r] -> (RTyCon, [RPVar])
appRTyCon tce tyi rc ts = F.notracepp _msg (resTc, ps'')
  where
    _msg  = "appRTyCon-family: " ++ showpp (Ghc.isFamilyTyCon c, Ghc.tyConRealArity c, toType False <$> ts)
    resTc = RTyCon c ps'' (rtc_info rc'')
    c     = rtc_tc rc

    (rc', ps') = rTyConWithPVars tyi rc (rTypeSort tce <$> ts)
    -- TODO:faminst-preds rc'   = M.lookupDefault rc c (tcmTyRTy tyi)
    -- TODO:faminst-preds ps'   = rTyConPVs rc'

    -- TODO:faminst-preds: these substitutions may be WRONG if we are using FAMINST.
    ps'' = flip (foldr (subtWithSort (Just (typeSort tce . toType True)))) (zip (RTV <$> αs) ts') <$> ps'
      where
        ts' = if null ts then rVar <$> βs else toRSort <$> ts
        αs  = GM.tyConTyVarsDef (rtc_tc rc')
        βs  = GM.tyConTyVarsDef c

    rc''  = if isNumeric tce rc' then addNumSizeFun rc' else rc'

rTyConWithPVars :: TyConMap -> RTyCon -> [F.Sort] -> (RTyCon, [RPVar])
rTyConWithPVars tyi rc ts = case famInstTyConMb tyi rc ts of
  Just fiRc    -> (rc', rTyConPVs fiRc)       -- use the PVars from the family-instance TyCon
  Nothing      -> (rc', ps')                  -- use the PVars from the origin          TyCon
  where
    (rc', ps') = plainRTyConPVars tyi rc

-- | @famInstTyConMb rc args@ uses the @RTyCon@ AND @args@ to see if
--   this is a family instance @RTyCon@, and if so, returns it.
--   see [NOTE:FamInstPredVars]
--   eg: 'famInstTyConMb tyi Field [Blob, a]' should give 'Just R:FieldBlob'

famInstTyConMb :: TyConMap -> RTyCon -> [F.Sort] -> Maybe RTyCon
famInstTyConMb tyi rc ts = do
  let c = rtc_tc rc
  n    <- M.lookup c      (tcmFtcArity tyi)
  M.lookup (c, take n ts) (tcmFIRTy    tyi)

famInstTyConType :: Ghc.TyCon -> Maybe Ghc.Type
famInstTyConType c = uncurry Ghc.mkTyConApp <$> famInstArgs c

-- | @famInstArgs c@ destructs a family-instance @TyCon@ into its components, e.g.
--   e.g. 'famInstArgs R:FieldBlob' is @(Field, [Blob])@

famInstArgs :: Ghc.TyCon -> Maybe (Ghc.TyCon, [Ghc.Type])
famInstArgs c = case Ghc.tyConFamInst_maybe c of
    Just (c', ts) -> F.notracepp ("famInstArgs: " ++ F.showpp (c, cArity, ts))
                     $ Just (c', take (length ts - cArity) ts)
    Nothing       -> Nothing
    where
      cArity      = Ghc.tyConRealArity c

-- TODO:faminst-preds: case Ghc.tyConFamInst_maybe c of
-- TODO:faminst-preds:   Just (c', ts) -> F.tracepp ("famInstTyConType: " ++ F.showpp (c, Ghc.tyConArity c, ts))
-- TODO:faminst-preds:                    $ Just (famInstType (Ghc.tyConArity c) c' ts)
-- TODO:faminst-preds:   Nothing       -> Nothing

-- TODO:faminst-preds: famInstType :: Int -> Ghc.TyCon -> [Ghc.Type] -> Ghc.Type
-- TODO:faminst-preds: famInstType n c ts = Ghc.mkTyConApp c (take (length ts - n) ts)




-- | @plainTyConPVars@ uses the @TyCon@ to return the
--   "refined" @RTyCon@ and @RPVars@ from the refined
--   'data' definition for the @TyCon@, e.g. will use
--   'List Int' to return 'List<p> Int' (if List has an abs-ref).
plainRTyConPVars :: TyConMap -> RTyCon -> (RTyCon, [RPVar])
plainRTyConPVars tyi rc = (rc', rTyConPVs rc')
  where
    rc' = M.lookupDefault contextual (rtc_tc rc) (tcmTyRTy tyi)
    known = M.map (varianceTyArgs . rtc_info) (tcmTyRTy tyi)
    inferred = makeTyConVariances known M.empty [rtc_tc rc]
    contextual = rc{rtc_info = (rtc_info rc){varianceTyArgs = M.findWithDefault [] (rtc_tc rc) inferred}}



-- RJ: The code of `isNumeric` is incomprehensible.
-- Please fix it to use intSort instead of intFTyCon
isNumeric :: TCEmb TyCon -> RTyCon -> Bool
isNumeric tce c = F.isNumeric mySort
  where
    -- mySort      = M.lookupDefault def rc tce
    mySort      = maybe def fst (F.tceLookup rc tce)
    def         = FTC . symbolFTycon . dummyLoc . tyConName $ rc
    rc          = rtc_tc c

addNumSizeFun :: RTyCon -> RTyCon
addNumSizeFun c
  = c {rtc_info = (rtc_info c) {sizeFunction = Just IdSizeFun } }


generalize :: (Eq tv, Monoid r) => RType c tv r -> RType c tv r
generalize t = mkUnivs (map (, mempty) (freeTyVars t)) [] t

allTyVars :: (Ord tv) => RType c tv r -> [tv]
allTyVars = sortNub . allTyVars'

allTyVars' :: (Eq tv) => RType c tv r -> [tv]
allTyVars' t = fmap ty_var_value $ vs ++ vs'
  where
    vs      = map fst . fst3 . bkUniv $ t
    vs'     = freeTyVars t


freeTyVars :: Eq tv => RTypeV v c tv r -> [RTVar Symbol v c tv]
freeTyVars (RAllP _ t)       = freeTyVars t
freeTyVars (RAllT α t _)     = freeTyVars t L.\\ [α]
freeTyVars (RFun _ _ t t' _) = freeTyVars t `L.union` freeTyVars t'
freeTyVars (RApp _ ts _ _)   = L.nub $ concatMap freeTyVars ts
freeTyVars (RVar α _)        = [makeRTVar α]
freeTyVars (REx _ tx t)      = freeTyVars tx `L.union` freeTyVars t
freeTyVars (RLit _)          = []
freeTyVars (RExprArg _)      = []
freeTyVars (RAppTy t t' _)   = freeTyVars t `L.union` freeTyVars t'
freeTyVars (RHole _)         = []
freeTyVars (RRTy e _ _ t)    = L.nub $ concatMap freeTyVars (t:(snd <$> e))


tyClasses :: (OkRT RTyCon tv r) => RType RTyCon tv r -> [(Class, [RType RTyCon tv r])]
tyClasses (RAllP _ t)     = tyClasses t
tyClasses (RAllT _ t _)   = tyClasses t
tyClasses (REx _ _ t)     = tyClasses t
tyClasses (RFun _ _ t t' _) = tyClasses t ++ tyClasses t'
tyClasses (RAppTy t t' _) = tyClasses t ++ tyClasses t'
tyClasses (RApp c ts _ _)
  | Just cl <- tyConClass_maybe $ rtc_tc c
  = [(cl, ts)]
  | otherwise
  = []
tyClasses (RVar _ _)      = []
tyClasses (RRTy _ _ _ t)  = tyClasses t
tyClasses (RLit _)        = []
tyClasses (RHole _)       = []
tyClasses t               = panic Nothing ("RefType.tyClasses cannot handle" ++ F.showpp t)


--------------------------------------------------------------------------------
-- TODO: Rewrite subsTyvars with Traversable
--------------------------------------------------------------------------------

subsTyVarsMeet
  :: (Eq tv, Foldable t, Hashable tv, IsReft r, Eq (ReftVar r), TyConable c, Binder b, Symbolic b, Meet r,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) c, SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) r, SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) Sort,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) (RTypeBV b v c tv (NoReftBV b v)), FreeVar c tv,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) tv,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) (RTVar b v c tv))
  => t (tv, RTypeBV b v c tv (NoReftBV b v), RTypeBV b v c tv r) -> RTypeBV b v c tv r -> RTypeBV b v c tv r
subsTyVarsMeet        = subsTyVars True

subsTyVarsNoMeet
  :: (Eq tv, Foldable t, Hashable tv, IsReft r, Eq (ReftVar r), TyConable c, Binder b, Symbolic b, Meet r,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) c, SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) r, SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) Sort,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) (RTypeBV b v c tv (NoReftBV b v)), FreeVar c tv,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) tv,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) (RTVar b v c tv))
  => t (tv, RTypeBV b v c tv (NoReftBV b v), RTypeBV b v c tv r) -> RTypeBV b v c tv r -> RTypeBV b v c tv r
subsTyVarsNoMeet      = subsTyVars False

subsTyVarNoMeet
  :: (Eq tv, Hashable tv, IsReft r, Eq (ReftVar r), TyConable c, Binder b, Symbolic b, Meet r,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) c, SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) r, SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) Sort,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) (RTypeBV b v c tv (NoReftBV b v)), FreeVar c tv,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) tv,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) (RTVar b v c tv))
  => (tv, RTypeBV b v c tv (NoReftBV b v), RTypeBV b v c tv r) -> RTypeBV b v c tv r -> RTypeBV b v c tv r
subsTyVarNoMeet       = subsTyVar False

subsTyVarMeet
  :: (Eq tv, Hashable tv, IsReft r, Eq (ReftVar r), TyConable c, Binder b, Symbolic b, Meet r,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) c, SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) r, SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) Sort,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) (RTypeBV b v c tv (NoReftBV b v)), FreeVar c tv,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) tv,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) (RTVar b v c tv))
  => (tv, RTypeBV b v c tv (NoReftBV b v), RTypeBV b v c tv r) -> RTypeBV b v c tv r -> RTypeBV b v c tv r
subsTyVarMeet         = subsTyVar True

subsTyVarMeet'
  :: (Eq tv, Hashable tv, IsReft r, Eq (ReftVar r), TyConable c, Binder b, Symbolic b, Meet r,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) c, SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) r, SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) Sort,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) (RTypeBV b v c tv (NoReftBV b v)), FreeVar c tv,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) tv,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) (RTVar b v c tv))
  => (tv, RTypeBV b v c tv r) -> RTypeBV b v c tv r -> RTypeBV b v c tv r
subsTyVarMeet' (α, t) = subsTyVarMeet (α, toRSort t, t)

-- Concrete sort instantiation needs the owner's embeddings. Structural
-- substitution transports only variable coordinates in retained expressions.
subsTyVarMeetWith :: TCEmb TyCon -> (RTyVar, SpecType) -> SpecType -> SpecType
subsTyVarMeetWith embeddings (variable, ty) =
  subsFree (Just (typeSort embeddings . toType True)) True S.empty (variable, toRSort ty, ty)

subsTyVars
  :: (Eq tv, Foldable t, Hashable tv, IsReft r, Eq (ReftVar r), TyConable c, Binder b, Symbolic b, Meet r,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) c, SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) r, SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) Sort,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) (RTypeBV b v c tv (NoReftBV b v)), FreeVar c tv,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) tv,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) (RTVar b v c tv))
  => Bool
  -> t (tv, RTypeBV b v c tv (NoReftBV b v), RTypeBV b v c tv r)
  -> RTypeBV b v c tv r
  -> RTypeBV b v c tv r
subsTyVars meet' ats t = foldl' (flip (subsTyVar meet')) t ats

subsTyVar
  :: (Eq tv, Hashable tv, IsReft r, Eq (ReftVar r), TyConable c, Binder b, Symbolic b, Meet r,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) c, SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) r, SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) Sort,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) (RTypeBV b v c tv (NoReftBV b v)), FreeVar c tv,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) tv,
      SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) (RTVar b v c tv))
  => Bool
  -> (tv, RTypeBV b v c tv (NoReftBV b v), RTypeBV b v c tv r)
  -> RTypeBV b v c tv r
  -> RTypeBV b v c tv r
subsTyVar meet'        = subsFree Nothing meet' S.empty

subsFree ::
    ( Eq tv
    , Hashable tv
    , IsReft r
    , Eq (ReftVar r)
    , TyConable c
    , Binder b
    , Symbolic b
    , Meet r
    , SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) c
    , SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) r
    , SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) Sort
    , SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) (RTypeBV b v c tv (NoReftBV b v))
    , FreeVar c tv
    , SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) tv
    , SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) (RTVar b v c tv)
    ) =>
    Maybe (RTypeBV b v c tv (NoReftBV b v) -> Sort) ->
    Bool ->
    S.HashSet tv ->
    (tv, RTypeBV b v c tv (NoReftBV b v), RTypeBV b v c tv r) ->
    RTypeBV b v c tv r ->
    RTypeBV b v c tv r
subsFree image = subsFreeWith image preserveBound (subtWithSort image) meet top isTauto
  where
    preserveBound substitution binder = (subtWithSort image substitution binder, ty_var_value binder)

{- | Substitute a retained type coordinate through the same structural visitor.
Refinement actions must commute with their interpretation. In particular,
conjunction must compose source predicates, not merely overwrite readback.
The binder action returns the transported binder and the coordinate protected
in its body: free instantiation protects the original owner; alpha-renaming
protects the new owner and transports occurrences of the old owner.
-}
subsFreeWith ::
    ( Eq tv
    , Hashable tv
    , TyConable c
    , Binder b
    , Symbolic b
    , SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) c
    , SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) Sort
    , SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) (RTypeBV b v c tv (NoReftBV b v))
    , FreeVar c tv
    , SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) tv
    , SubsTy tv (RTypeBV b v c tv (NoReftBV b v)) (RTVar b v c tv)
    ) =>
    Maybe (RTypeBV b v c tv (NoReftBV b v) -> Sort) ->
    ((tv, RTypeBV b v c tv (NoReftBV b v)) -> RTVar b v c tv -> (RTVar b v c tv, tv)) ->
    ((tv, RTypeBV b v c tv (NoReftBV b v)) -> r -> r) ->
    (r -> r -> r) ->
    (r -> r) ->
    (r -> Bool) ->
    Bool ->
    S.HashSet tv ->
    (tv, RTypeBV b v c tv (NoReftBV b v), RTypeBV b v c tv r) ->
    RTypeBV b v c tv r ->
    RTypeBV b v c tv r
subsFreeWith image scopeBinder act combine empty trivial = go
  where
    -- Replacements are required to be fresh for retained binders. The bound set
    -- protects the substituted coordinate, including every retained annotation.
    go _ s (α, _, _) t | α `S.member` s = t
    go m s z@(α, τ, _) (RAllP π t) =
        RAllP (subtWithSort image (α, τ) π) (go m s z t)
    go m s z@(a, τ, _) (RAllT α t r) =
        RAllT α' (go m (protected `S.insert` s) z t) (act (a, τ) r)
      where
        (α', protected) = scopeBinder (a, τ) α
    go m s z@(α, τ, _) (RFun x i t t' r) =
        RFun x i (go m s z t) (go m s z t') (act (α, τ) r)
    go m s z@(α, τ, _) (RApp c ts rs r) =
        RApp c' (go m s z <$> ts) (prop m s z <$> rs) (act (α, τ) r)
      where
        z' = (α, τ) -- UNIFY: why instantiating INSIDE parameters?
        c' = if α `S.member` s then c else subtWithSort image z' c
    go meet' s (α', τ, t') (RVar α r)
        | α == α' && not (α `S.member` s) =
            if meet' then strengthenWithTest trivial combine t' (act (α, τ) r) else t'
        | otherwise =
            RVar (subtWithSort image (α', τ) α) (act (α', τ) r)
    go m s z (REx x t t') =
        REx x (go m s z t) (go m s z t')
    go m s z@(α, τ, _) (RAppTy t t' r) =
        appTy m s (go m s z t) (go m s z t') (act (α, τ) r)
    go _ _ _ t@(RLit _) =
        t
    go _ _ (α, τ, _) (RExprArg e) =
        RExprArg (subtWithSort image (α, τ) <$> e)
    go m s z@(α, τ, _) (RRTy e r o t) =
        RRTy (fmap (go m s z) <$> e) (act (α, τ) r) o (go m s z t)
    go _ _ (α, τ, _) (RHole r) =
        RHole (act (α, τ) r)

    gos m s zs t = foldl' (flip (go m s)) t zs

    -- GHC INVARIANT: RApp is Type Application to something other than TYCon

    appTy m s (RApp c ts rs r) t' r' =
        app m s c (ts ++ [t']) rs r r'
    appTy _ _ t t' r' =
        RAppTy t t' r'

    -- \| @app@ is the refined variant of GHC's @mkTyConApp@ which ensures that
    --    that applications of the "function" type constructor are normalized to
    --    the special case @FunTy _@ representation. The extra `_rep1`, and `_rep2`
    --    parameters come from the "levity polymorphism" changes in GHC 8.6 (?)
    --    See [NOTE:Levity-Polymorphism]

    app m s c ts rs r r'
        | isFun c
        , [_m, _rep1, _rep2, t1, t2] <- ts =
            RFun wildcard defRFInfo t1 t2 (checkFun r')
        | otherwise =
            gos m s zs (RApp c ts rs (combine r r'))
      where
        zs = [(tv, toRSort t, t) | (tv, t) <- zip (freeVars c) ts]

    prop _ _ (α', τ', _) (RProp ss (RHole r)) =
        RProp (fmap (subtWithSort image (α', τ')) <$> ss) (RHole (act (α', τ') r))
    prop m s (α', τ', t') (RProp ss t) =
        RProp (fmap (subtWithSort image (α', τ')) <$> ss) $ go m s (α', τ', fmap empty t') t

    checkFun r
        | trivial r = r
        | otherwise = panic Nothing "RefType.refAppTyToFun"

{-| [NOTE:Levity-Polymorphism]

     Thanks to Joachim Brietner and Simon Peyton-Jones!
     With GHC's "levity polymorphism feature", see more here

         https://stackoverflow.com/questions/35318562/what-is-levity-polymorphism

     The function type constructor actually has type

        (->) :: forall (r1::RuntimeRep) (r2::RuntimeRep).  TYPE r1 -> TYPE r2 -> TYPE LiftedRep

     so we have to be careful to follow GHC's @mkTyConApp@

        https://hackage.haskell.org/package/ghc-8.6.4/docs/src/Type.html#mkTyConApp

     which normalizes applications of the `FunTyCon` constructor to use the special
     case `FunTy _` representation thus, so that we are not stuck with incompatible
     representations e.g.

        thing -> thing                                                  ... (using RFun)

     and

        (-> 'GHC.Types.LiftedRep 'GHC.Types.LiftedRep thing thing)      ... (using RApp)


     More details from Joachim Brietner:

     Now you might think that the function arrow has the following kind: `(->) :: * -> * -> *`.
     But that is not the full truth: You can have functions that accept or return things with
     different representations than just the usual lifted one.

     So the function arrow actually has kind `(->) :: forall r1 r2. TYPE r1 -> TYPE r2 -> *`.
     And in `(-> 'GHC.Types.LiftedRep 'GHC.Types.LiftedRep thing thing)`  you see this spelled
     out explicitly. But it really is just `(thing -> thing)`, just printed with more low-level detail.

     Also see

       • https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html#levity-polymorphism
       • and other links from https://stackoverflow.com/a/35320729/946226 (edited)
 -}


--------------------------------------------------------------------------------
-- | Type Substitutions --------------------------------------------------------
--------------------------------------------------------------------------------

subts :: (SubsTy tv ty c) => [(tv, ty)] -> c -> c
subts = flip (foldr subt)

instance SubsTy RTyVar (RType RTyCon RTyVar NoReft) RTyVar where
  subtWithSort _ (RTV x, t) (RTV z)
    | isTyVar z
    , x `elemVarSet` tyCoVarsOfType (tyVarKind z) =
        RTV (setVarType z $ Ghc.substTyWith [x] [toType False t] (tyVarKind z))
  subtWithSort _ _ v =
    v

instance SubsTy RTyVar (RType RTyCon RTyVar NoReft) (RTVar Symbol Symbol RTyCon RTyVar) where
  subtWithSort image su rty = rty{ty_var_value = subtWithSort image su $ ty_var_value rty, ty_var_info = info}
   where
    info = case ty_var_info rty of
      i@RTVInfo{} -> i{rtv_kind = subtWithSort image su $ rtv_kind i}
      i@RTVNoInfo{} -> i


instance SubsTy BTyVar (RType c BTyVar NoReft) BTyVar where
  subtWithSort _ _ = id

instance SubsTy BTyVar (RType c BTyVar NoReft) (RType c BTyVar NoReft) => SubsTy BTyVar (RType c BTyVar NoReft) (RTVar Symbol Symbol c BTyVar) where
  subtWithSort image su variable = variable{ty_var_info = info}
    where
      info = case ty_var_info variable of
        known@RTVInfo{} -> known{rtv_kind = subtWithSort image su (rtv_kind known)}
        unknown@RTVNoInfo{} -> unknown

instance F.Symbolic tv => SubsTy tv ty NoReft   where
  subtWithSort _ _ = id

instance F.Symbolic tv => SubsTy tv ty Symbol where
  subtWithSort _ _ = id



instance (Symbolic tv, SubsTy tv ty Expr) => SubsTy tv ty Reft where
  subtWithSort image su (Reft (x, e)) = Reft (x, subtWithSort image su e)

instance SubsTy Symbol Symbol r => SubsTy Symbol Symbol (BRType r) where
  subtWithSort image su@(x,y) (RVar (BTV v) r)
    | x == val v = RVar (BTV (y <$ v)) (subtWithSort image su r)
    | otherwise = RVar (BTV v) (subtWithSort image su r)
  subtWithSort image su@(x, _) (RAllT (RTVar (BTV v) i) t r)
    = RAllT (RTVar (BTV v) info) body (subtWithSort image su r)
    where
      body | x == val v = t
           | otherwise = subtWithSort image su t
      info = case i of
        known@RTVInfo{} -> known{rtv_kind = subtWithSort image su (rtv_kind known)}
        unknown@RTVNoInfo{} -> unknown
  subtWithSort image su (RFun x i t1 t2 r) = RFun x i (subtWithSort image su t1) (subtWithSort image su t2) (subtWithSort image su r)
  subtWithSort image su (RAllP p t) = RAllP (subtWithSort image su p) (subtWithSort image su t)
  subtWithSort image su (RApp c ts ps r) = RApp c (subtWithSort image su <$> ts) (subtWithSort image su <$> ps) (subtWithSort image su r)
  subtWithSort image su (REx x t1 t2) = REx x (subtWithSort image su t1) (subtWithSort image su t2)
  subtWithSort _ _ (RLit l) = RLit l
  subtWithSort image su (RExprArg e) = RExprArg (subtWithSort image su <$> e)
  subtWithSort image su (RAppTy t1 t2 r) = RAppTy (subtWithSort image su t1) (subtWithSort image su t2) (subtWithSort image su r)
  subtWithSort image su (RRTy e r o t) = RRTy [(x, subtWithSort image su p) | (x,p) <- e] (subtWithSort image su r) o (subtWithSort image su t)
  subtWithSort image su (RHole r) = RHole (subtWithSort image su r)

instance SubsTy Symbol Symbol r => SubsTy Symbol Symbol (RTProp BTyCon BTyVar r) where
  subtWithSort image su (RProp e t) = RProp [(x, subtWithSort image su xt) | (x,xt) <- e] (subtWithSort image su t)


instance (F.Symbolic b, SubsTy tv ty Sort) => SubsTy tv ty (F.ExprBV b v) where
  subtWithSort _ (variable, _) expression@(ETAbs _ binder)
    | symbol variable == symbol binder = expression
  subtWithSort image su (ECon (F.L literal s)) = ECon (F.L literal (subtWithSort image su s))
  subtWithSort image su (ELam (x, s) e) = ELam (x, subtWithSort image su s) $ subtWithSort image su e
  subtWithSort image su (EApp e1 e2)    = EApp (subtWithSort image su e1) (subtWithSort image su e2)
  subtWithSort image su (ENeg e)        = ENeg (subtWithSort image su e)
  subtWithSort image su (PNot e)        = PNot (subtWithSort image su e)
  subtWithSort image su (EBin b e1 e2)  = EBin b (subtWithSort image su e1) (subtWithSort image su e2)
  subtWithSort image su (F.ELet x e1 e2) = F.ELet x (subtWithSort image su e1) (subtWithSort image su e2)
  subtWithSort image su (EIte e e1 e2)  = EIte (subtWithSort image su e) (subtWithSort image su e1) (subtWithSort image su e2)
  subtWithSort image su (ECst e s)      = ECst (subtWithSort image su e) (subtWithSort image su s)
  subtWithSort image su (ETApp e s)     = ETApp (subtWithSort image su e) (subtWithSort image su s)
  subtWithSort image su (ETAbs e x)     = ETAbs (subtWithSort image su e) x
  subtWithSort image su (PAnd es)       = PAnd (subtWithSort image su <$> es)
  subtWithSort image su (POr  es)       = POr  (subtWithSort image su <$> es)
  subtWithSort image su (PImp e1 e2)    = PImp (subtWithSort image su e1) (subtWithSort image su e2)
  subtWithSort image su (PIff e1 e2)    = PIff (subtWithSort image su e1) (subtWithSort image su e2)
  subtWithSort image su (PAtom b e1 e2) = PAtom b (subtWithSort image su e1) (subtWithSort image su e2)
  subtWithSort image su (PAll xes e)    = PAll [(x, subtWithSort image su s) | (x, s) <- xes] (subtWithSort image su e)
  subtWithSort image su (PExist xes e)  = PExist [(x, subtWithSort image su s) | (x, s) <- xes] (subtWithSort image su e)
  subtWithSort image su (F.ECoerc s t e) = F.ECoerc (subtWithSort image su s) (subtWithSort image su t) (subtWithSort image su e)
  subtWithSort image su (F.PKVar k sorts values) = F.PKVar k (subtWithSort image su <$> sorts) (F.mapKVarSubst (subtWithSort image su) values)
  subtWithSort image _ e                = e

instance (SubsTy tv ty a, SubsTy tv ty b) => SubsTy tv ty (a, b) where
  subtWithSort image su (x, y) = (subtWithSort image su x, subtWithSort image su y)

instance SubsTy Symbol Symbol Sort where
  subtWithSort image (old, new) s
    | old `S.member` F.sortSymbols s = F.sortSubst (F.mkSortSubst [(old, maybe (FObj new) ($ new) image)]) s
    | otherwise = s

instance SubsTy BTyVar (RType BTyCon BTyVar NoReft) Sort where
  subtWithSort (Just project) (v, replacement) s
    | symbol v `S.member` F.sortSymbols s = F.sortSubst (F.mkSortSubst [(symbol v, project replacement)]) s
    | otherwise = s
  subtWithSort Nothing (v, RVar α _) s
    | symbol v `S.member` F.sortSymbols s = F.sortSubst (F.mkSortSubst [(symbol v, FObj (symbol α))]) s
  subtWithSort _ _ s = s


instance SubsTy Symbol RSort Sort where
  subtWithSort (Just project) (v, replacement) s
    | v `S.member` F.sortSymbols s = F.sortSubst (F.mkSortSubst [(v, project replacement)]) s
    | otherwise = s
  subtWithSort Nothing (v, RVar α _) s
    | v `S.member` F.sortSymbols s = F.sortSubst (F.mkSortSubst [(v, FObj (symbol α))]) s
  subtWithSort _ _ s = s


instance SubsTy RTyVar RSort Sort where
  subtWithSort (Just project) (v, replacement) s
    | symbol v `S.member` F.sortSymbols s = F.sortSubst (F.mkSortSubst [(symbol v, project replacement)]) s
    | otherwise = s
  subtWithSort image (v, sv@RVar{}) s
    | symbol v `S.member` F.sortSymbols s =
        F.sortSubst (F.mkSortSubst [(symbol v, typeSort mempty (toType True sv))]) s
  subtWithSort _ _ s = s

instance (SubsTy tv ty payload, SubsTy tv ty (F.ExprBV b v)) => SubsTy tv ty (PVarBV b v payload) where
  subtWithSort image su (PV n pvk xts) = PV n (subtWithSort image su pvk) [(subtWithSort image su t, x, subtWithSort image su y) | (t,x,y) <- xts]

instance SubsTy RTyVar RSort RTyCon where
   subtWithSort image z c = RTyCon tc ps' i
     where
       tc   = rtc_tc c
       ps'  = subtWithSort image z <$> rTyConPVs c
       i    = rtc_info c

instance SubsTy RTyVar RSort SpecType where
  subtWithSort image (α, τ) = subsFree image True S.empty (α, τ, ofRSort τ)

instance SubsTy TyVar Type SpecType where
  subtWithSort image (α, τ) = subsFree (fmap (\project -> project . toType False) image) True S.empty (RTV α, ofType τ, ofType τ)

instance SubsTy RTyVar RSort RSort where
  subtWithSort image (α, τ) = subsFree image True S.empty (α, τ, τ)

instance (Symbolic tv, SubsTy tv ty (F.ExprBV b v)) => SubsTy tv ty (PredicateBV b v) where
  subtWithSort image su (Pr predicates) = Pr [predicate{pargs = [(t, x, subtWithSort image su expression) | (t, x, expression) <- pargs predicate]} | predicate <- predicates]

instance (Symbolic tv, SubsTy tv ty Reft, SubsTy tv ty Predicate) => SubsTy tv ty UReft where
  subtWithSort image su r = r {ur_reft = subtWithSort image su $ ur_reft r, ur_pred = subtWithSort image su $ ur_pred r}

-- Here the "String" is a Bare-TyCon. TODO: wrap in newtype
instance SubsTy BTyVar BSort BTyCon where
  subtWithSort _ _ t = t

instance SubsTy BTyVar BSort BSort where
  subtWithSort image (α, τ) = subsFree image True S.empty (α, τ, τ)

instance (SubsTy tv ty (RType c tv UReft), SubsTy tv ty (RType c tv NoReft)) => SubsTy tv ty (RTProp c tv UReft)  where
  subtWithSort image m (RProp ss t) = RProp (fmap (subtWithSort image m) <$> ss) (subtWithSort image m t)

subvUReft     :: (UsedPVar -> UsedPVar) -> UReft -> UReft
subvUReft f (MkUReft r p) = MkUReft r (subvPredicate f p)

subvPredicate :: (UsedPVar -> UsedPVar) -> Predicate -> Predicate
subvPredicate f (Pr pvs) = Pr (f <$> pvs)

--------------------------------------------------------------------------------
ofType :: IsReft r => Type -> RRType r
--------------------------------------------------------------------------------
ofType      = ofType_ $ TyConv
  { tcFVar  = rVar
  , tcFTVar = rTVar
  , tcFApp  = \c ts -> rApp c ts [] trueReft
  , tcFLit  = RLit
  }

--------------------------------------------------------------------------------
bareOfType :: IsReft r => Type -> BRType r
--------------------------------------------------------------------------------
bareOfType  = ofType_ $ TyConv
  { tcFVar  = (`RVar` trueReft) . BTV . fmap symbol . GM.locNamedThing
  , tcFTVar = bTVar
  , tcFApp  = \c ts -> bApp c ts [] trueReft
  , tcFLit  = RLit
  }

--------------------------------------------------------------------------------
ofType_ :: IsReft r => TyConv c tv r -> Type -> RType c tv r
--------------------------------------------------------------------------------
ofType_ tx = go . expandTypeSynonyms
  where
    go (TyVarTy α)
      = tcFVar tx α
    go (FunTy _ _ τ τ')
      = rFun dummySymbol (go τ) (go τ')
    go (ForAllTy (Bndr α _) τ)
      = RAllT (tcFTVar tx α) (go τ) trueReft
    go (TyConApp c τs)
      | Just (αs, τ) <- Ghc.synTyConDefn_maybe c
      = go (substTyWith αs τs τ)
      | otherwise
      = tcFApp tx c (go <$> τs) -- [] mempty
    go (AppTy t1 t2)
      = RAppTy (go t1) (ofType_ tx t2) trueReft
    go (LitTy x)
      = tcFLit tx x
    go (CastTy t _)
      = go t
    go (CoercionTy _)
      = errorstar "Coercion is currently not supported"

data TyConv c tv r = TyConv
  { tcFVar  :: TyVar -> RType c tv r
  , tcFTVar :: TyVar -> RTVar Symbol Symbol c tv
  , tcFApp  :: TyCon -> [RType c tv r] -> RType c tv r
  , tcFLit  :: TyLit -> RType c tv r
  }

--------------------------------------------------------------------------------
-- | Converting to Fixpoint ----------------------------------------------------
--------------------------------------------------------------------------------


instance Expression Var where
  expr   = eVar

-- TODO: turn this into a map lookup?
-- Arguments are the physical worker fields (including case binders). The
-- prepared constructor contract separately reconstructs the source identity.
dataConReft ::  DataCon -> [Symbol] -> Reft
dataConReft c []
  | c == trueDataCon
  = predReft $ eProp vv_
  | c == falseDataCon
  = predReft $ PNot $ eProp vv_

dataConReft c [x]
  | c == intDataCon
  = symbolReft x -- OLD (vv_, [RConc (PAtom Eq (EVar vv_) (EVar x))])
dataConReft c _
  | not $ isBaseDataCon c
  = mempty
dataConReft c xs
  = exprReft dcValue -- OLD Reft (vv_, [RConc (PAtom Eq (EVar vv_) dcValue)])
  where
    dcValue
        | null xs && null (dataConUnivTyVars c) =
            EVar $ symbol (dataConWorkId c)
        | otherwise =
            mkEApp (dummyLoc $ symbol (dataConWorkId c)) (eVar <$> xs)

isBaseDataCon :: DataCon -> Bool
isBaseDataCon c = all (isBaseTy . irrelevantMult) (dataConOrigArgTys c ++ dataConRepArgTys c)

isBaseTy :: Type -> Bool
isBaseTy (TyVarTy _)      = True
isBaseTy (AppTy _ _)      = False
isBaseTy (TyConApp _ ts)  = all isBaseTy ts
isBaseTy FunTy{}          = False
isBaseTy (ForAllTy _ _)   = False
isBaseTy (LitTy _)        = True
isBaseTy (CastTy _ _)     = False
isBaseTy (CoercionTy _)   = False


dataConMsReft :: (IsReft r, ReftBind r ~ v, ReftVar r ~ v, F.Refreshable v) => RTypeBV v v c tv r -> [v] -> ReftBV v v
dataConMsReft ty ys  = subst su (rTypeReft (ignoreOblig $ ty_res trep))
  where
    trep = toRTypeRep ty
    xs   = ty_binds trep
    ts   = ty_args  trep
    su   = mkSubst $ [(x, EVar y) | ((x, _), y) <- zip (zip xs ts) ys]

--------------------------------------------------------------------------------
-- | Embedding RefTypes --------------------------------------------------------
--------------------------------------------------------------------------------

type ToTypeable r = (IsReft r, ReftBind r ~ Symbol, ReftVar r ~ Symbol, PPrint r, PPrint (RTProp RTyCon RTyVar r), SubsTy RTyVar (RRType NoReft) r)

-- TODO: remove toType, generalize typeSort
-- YL: really should take a type-level Bool
specTypeToQueryType :: SpecType -> Type
specTypeToQueryType = go
  where
    go (RLit l) = LitTy l
    go (RVar (RTV tv) _) = mkTyVarTy tv
    go (RFun _ _ domain result _)
        | isClassType domain = Ghc.mkInvisFunTy (go domain) (go result)
        | otherwise = Ghc.mkVisFunTyMany (go domain) (go result)
    go (RAllT (ty_var_value -> RTV tv) rest _) = Ghc.mkSpecForAllTy tv (go rest)
    go (RAllP _ rest) = go rest
    go (RApp RTyCon{rtc_tc = tc} arguments _ _) = mkTyConApp tc (map go (filter notExprArg arguments))
    go (REx _ _ result) = go result
    go (RAppTy _ RExprArg{} _) = impossible Nothing "RExprArg in generated predicate telescope"
    go (RAppTy function argument _) = Ghc.mkAppTy (go function) (go argument)
    go (RRTy _ _ _ rest) = go rest
    go ty = panic Nothing ("Unsupported generated predicate telescope: " ++ F.showpp ty)

toType  :: (ToTypeable r) => Bool -> RRType r -> Type
toType useRFInfo (RFun _ _ t@(RApp c _ _ _) t' _)
  | useRFInfo && isErasable c = toType useRFInfo t'
    | otherwise =
        FunTy FTF_T_T ManyTy (toType useRFInfo t) (toType useRFInfo t')
  where
    isErasable = isEmbeddedDict
toType useRFInfo (RFun _ _ t t' _)
  = FunTy FTF_T_T ManyTy (toType useRFInfo t) (toType useRFInfo t')
toType useRFInfo (RAllT a t _) | RTV α <- ty_var_value a
  = ForAllTy (Bndr α Required) (toType useRFInfo t)
toType useRFInfo (RAllP _ t)
  = toType useRFInfo t
toType _ (RVar (RTV α) _)
  = TyVarTy α
toType useRFInfo (RApp RTyCon{rtc_tc = c} ts _ _)
  = TyConApp c (toType useRFInfo <$> filter notExprArg ts)
toType useRFInfo (REx _ _ t)
  = toType useRFInfo t
toType useRFInfo (RAppTy t (RExprArg _) _)
  = toType useRFInfo t
toType useRFInfo (RAppTy t t' _)
  = AppTy (toType useRFInfo t) (toType useRFInfo t')
toType _ t@(RExprArg _)
  = impossible Nothing $ "CANNOT HAPPEN: RefType.toType called with: " ++ showpp t
toType useRFInfo (RRTy _ _ _ t)
  = toType useRFInfo t
toType _ (RLit l)
  = LitTy l
toType _ (RHole _)
  = impossible Nothing "RefType.toType: unresolved refinement type hole"
-- toType t
--  = {- impossible Nothing -} Prelude.error $ "RefType.toType cannot handle: " ++ show t

--------------------------------------------------------------------------------
-- | Annotations and Solutions -------------------------------------------------
--------------------------------------------------------------------------------

rTypeSortedReft ::  (PPrint r, IsReft r, ReftBind r ~ Symbol, ReftVar r ~ Symbol, SubsTy RTyVar (RType RTyCon RTyVar NoReft) r)
                => TCEmb TyCon -> RRType r -> SortedReft
rTypeSortedReft emb t = RR (rTypeSort emb t) (rTypeReft t)

rTypeSort     ::  (PPrint r, IsReft r, ReftBind r ~ Symbol, ReftVar r ~ Symbol, SubsTy RTyVar (RType RTyCon RTyVar NoReft) r)
              => TCEmb TyCon -> RRType r -> Sort
rTypeSort tce = typeSort tce . toType True

--------------------------------------------------------------------------------
applySolution ::
    (Functor f) =>
    ResultScopes -> M.HashMap KVar (Delayed Expr) -> f SpecType -> Either String (f SpecType)
--------------------------------------------------------------------------------
applySolution scopes solution types = do
    scoped <- M.traverseWithKey withScope solution
    pure (fmap (fmap (mapReft' (appSolRefa scoped))) types)
  where
    withScope k predicate = case M.lookup k scopes of
        Nothing -> Left ("solution application: missing result scope for " ++ F.showpp k)
        Just formals
            | let names = map formalCanonical formals
            , S.size (S.fromList names) /= length names ->
                Left ("solution application: repeated canonical formal for " ++ F.showpp k)
            | otherwise -> Right (formals, predicate)
    mapReft' f (MkUReft (Reft (x, z)) p) = MkUReft (Reft (x, f z)) p

appSolRefa ::
    (Visitable t) =>
    M.HashMap KVar ([Formal], Delayed Expr) -> t -> t
appSolRefa solution = trans txK
  where
    txK (PKVar k tsu su) = case M.lookup k solution of
        Nothing -> PTop
        Just (formals, predicate) ->
            let su' = renameDomain formals su
                typed = FV.applyCoSub tsu (forceDelayed predicate)
             in rapierSubstExpr (substSymbolsSet su' `S.union` syms typed) su' typed
    txK p = p

    -- A source actual may supply several independently named canonical
    -- formals. Their names belong to the result, not to a naming convention.
    renameDomain formals su =
        Su $
            M.fromList
                [ (formalCanonical formal, M.lookupDefault (EVar source) source (fromKVarSubst su))
                | formal <- formals
                , let source = formalSource formal
                ]

--------------------------------------------------------------------------------
-- shiftVV :: Int -- SpecType -> Symbol -> SpecType
shiftVV ::
    ( TyConable c
    , IsReft r
    , Subable r
    , Variable r ~ Symbol
    , ReftBind r ~ Symbol
    , ReftVar r ~ Symbol
    ) =>
    RType c tv r -> Symbol -> RType c tv r
--------------------------------------------------------------------------------
shiftVV = shiftVVWith rTypeValueVar renameReftRoot subst1 subst1

{- | Align a constructor root without changing the carrier traversal. The
substitutions retain the scope of abstract-predicate formal arguments.
-}
shiftVVWith ::
    (RType c tv r -> Symbol) ->
    (r -> Symbol -> r) ->
    ([RType c tv r] -> (Symbol, Expr) -> [RType c tv r]) ->
    ([RTProp c tv r] -> (Symbol, Expr) -> [RTProp c tv r]) ->
    RType c tv r ->
    Symbol ->
    RType c tv r
shiftVVWith root rename substTypes substProps = go
  where
    go t@(RApp _ ts rs r) vv' =
        t{rt_args = substTypes ts (root t, EVar vv')}
            { rt_pargs = substProps rs (root t, EVar vv')
            }
            { rt_reft = rename r vv'
            }
    go t@(RFun _ _ _ _ r) vv' =
        t{rt_reft = rename r vv'}
    go t@(RAppTy _ _ r) vv' =
        t{rt_reft = rename r vv'}
    go t@(RVar _ r) vv' =
        t{rt_reft = rename r vv'}
    go t _ =
        t -- errorstar $ "shiftVV: cannot handle " ++ showpp t


--------------------------------------------------------------------------------
-- |Auxiliary Stuff Used Elsewhere ---------------------------------------------
--------------------------------------------------------------------------------

-- MOVE TO TYPES
instance (Show tv, Show ty) => Show (RTAlias tv ty) where
  show (RTA n as xs t) =
    printf "type %s %s %s = %s" (symbolString . getLHNameSymbol . val $ n)
      (unwords (show <$> as))
      (unwords (show <$> xs))
      (show t)

--------------------------------------------------------------------------------
-- | From Old Fixpoint ---------------------------------------------------------
--------------------------------------------------------------------------------
typeSort :: TCEmb TyCon -> Type -> Sort
typeSort tce = go
  where
    go :: Type -> Sort
    go t | Just expanded <- coreView t = go expanded
    go t@FunTy{}        = typeSortFun tce t
    go τ@(ForAllTy _ _) = typeSortForAll tce τ
    -- go (TyConApp c τs)  = fApp (tyConFTyCon tce c) (go <$> τs)
    go (TyConApp c τs)
      | Ghc.isFamilyTyCon c
      , Ghc.piResultTys (Ghc.tyConKind c) τs `Ghc.eqType` naturalTy
      = FInt
      | otherwise
      = tyConFTyCon tce c (go <$> τs)
    go (AppTy t1 t2)    = fApp (go t1) [go t2]
    go (TyVarTy tv)     = tyVarSort tv
    go (CastTy t _)     = go t
    go (LitTy (NumTyLit _)) = FInt
    -- Core lambda/coercion sorts must agree with RLit in the refinement-type
    -- path. Every Symbol literal, including the former hole spelling, is real.
    go (LitTy (StrTyLit _)) = tyConFTyCon tce listTyCon [tyConFTyCon tce charTyCon []]
    go τ                = FObj (typeUniqueSymbol τ)

-- | Interpret source constructors while their native owners and formal
-- coordinates are still available. This is not an inverse of 'typeSort':
-- logical primitives and private logical carriers have no native preimage.
-- Partial source constructors remain constructor values; a saturated native
-- application is interpreted before its formal coordinates are projected.
-- This does not give first-order 'Sort' a general constructor-function
-- meaning: non-prefix partial actions must remain native until application.
interpretEmbeddingSort :: (Symbol -> Maybe TyCon) -> TCEmb TyCon -> Sort -> Either LocSymbol Sort
interpretEmbeddingSort owner catalog = go S.empty Nothing
  where
    go active opaque original = case F.unFApp original of
      FTC constructor : arguments
        | Just native <- owner (symbol constructor)
        , let formals = Ghc.tyConTyVars native
              generic = Ghc.mkTyConApp native (Ghc.mkTyVarTy <$> formals)
              apply meaning actuals = fApp
                (F.sortSubst (F.mkSortSubst (zip (symbol <$> formals) actuals)) meaning)
                (drop (length formals) actuals)
        -- Definitional source reduction precedes interpretation of arguments:
        -- an alias can discard an argument or expose an identity action.
        , Just _ <- coreView generic
        , length arguments >= length formals ->
            go active opaque (transport (Ghc.isTYPEorCONSTRAINT (typeKind generic)) constructor (apply (typeSort mempty generic) arguments))
        | Just native <- owner (symbol constructor) -> do
            let formals = Ghc.tyConTyVars native
                generic = Ghc.mkTyConApp native (Ghc.mkTyVarTy <$> formals)
                valueCarrier = Ghc.isTYPEorCONSTRAINT (typeKind generic)
                coordinates = FObj . symbol <$> formals
                genericIdentity = fApp (FTC constructor) coordinates
                compose identity application
                  | application == identity = pure application
                  | otherwise = do
                      -- Compose the action on its own formals, not on already
                      -- interpreted operands. Substitution must not evaluate
                      -- an operand again as a fresh recursive reference.
                      composed <- go (S.insert native active) (Just native) application
                      if composed == identity || not (mentions native composed)
                        then pure composed
                        else Left (F.fTyconSymbol constructor)
            if Just native == opaque
              then fApp (FTC constructor) <$> traverse (go active opaque) arguments
              else if native `S.member` active
                then Left (F.fTyconSymbol constructor)
                else if length arguments >= length formals
                  then do
                    composed <- compose genericIdentity (transport valueCarrier constructor (typeSort catalog generic))
                    let demanded = F.sortSymbols composed
                        interpretActual formal actual
                          | symbol formal `S.member` demanded = go active opaque actual
                          | otherwise = pure actual
                        (inputs, surplus) = splitAt (length formals) arguments
                    actuals <- sequence (zipWith interpretActual formals inputs)
                    extras <- traverse (go active opaque) surplus
                    pure $ transport valueCarrier constructor $ fApp
                      (F.sortSubst (F.mkSortSubst (zip (symbol <$> formals) actuals)) composed)
                      extras
                  else do
                    actuals <- traverse (go active opaque) arguments
                    let unchanged = fApp (FTC constructor) actuals
                    case tceLookup native catalog of
                      Just (prefix, NoArgs) -> compose unchanged (transport False constructor (fApp prefix actuals))
                      _ -> pure unchanged
      _ -> case original of
        FAbs index body -> FAbs index <$> go active opaque body
        FFunc input output -> FFunc <$> go active opaque input <*> go active opaque output
        FApp function argument -> FApp <$> go active opaque function <*> go active opaque argument
        _ -> pure original

    transport valueCarrier constructor application = case F.unFApp application of
      FTC destination : values ->
        -- Numeric/string roles follow the existing scalar-carrier merge rule;
        -- attaching them to an applied Set/Map head changes sort admission.
        let located = F.symbolFTycon (symbol destination <$ F.fTyconSymbol constructor)
            metadata
              | valueCarrier && null values = F.mappendFTC constructor destination
              | otherwise = destination
        in fApp (FTC (F.mappendFTC located metadata)) values
      _ -> application

    mentions native meaning = case meaning of
      FTC constructor -> owner (symbol constructor) == Just native
      FAbs _ body -> mentions native body
      FFunc input output -> mentions native input || mentions native output
      FApp function argument -> mentions native function || mentions native argument
      _ -> False

-- | Compose a declared constructor action with its native formal arguments
-- before projecting source aliases or other declared embeddings. A genuinely
-- constant prefix keeps its partial-application representation.
interpretEmbedding :: (Symbol -> Maybe TyCon) -> TCEmb TyCon -> TyCon -> (Sort, TCArgs) -> Either LocSymbol (Sort, TCArgs)
interpretEmbedding owner catalog native (meaning, arguments) = do
    interpreted <- interpretEmbeddingSort owner catalog generic
    pure $ case (arguments, F.unFApp interpreted) of
      (NoArgs, constructor : actuals)
        | length actuals >= length formals
        , let count = length actuals - length formals
        , drop count actuals == coordinates
        , let prefix = fApp constructor (take count actuals)
        , S.null (S.intersection (S.fromList (symbol <$> formals)) (F.sortSymbols prefix)) ->
            (prefix, NoArgs)
      _ -> (interpreted, WithArgs)
  where
    formals = Ghc.tyConTyVars native
    coordinates = FObj . symbol <$> formals
    generic = case arguments of
      NoArgs -> fApp meaning coordinates
      WithArgs -> meaning

{- | A representation-preserving newtype embedding interprets its constructor
as identity only when its GENERIC source field and result have the same
logical type. Neither SMT carrier erasure nor a coincidental instantiation
establishes this law. Both the term interpreter and constructor equation
use this test, with the same free-sort coordinates as reflected functions.
-}
newtypeIdentitySort :: TCEmb TyCon -> DataCon -> Maybe Sort
newtypeIdentitySort tce dc
    | isNewTyCon (dataConTyCon dc)
    , [field] <- dataConOrigArgTys dc
    , let source = typeSort tce (irrelevantMult field)
    , source == typeSort tce (dataConOrigResTy dc) =
        Just (F.sortSubst substitution source)
    | otherwise =
        Nothing
  where
    variables = dataConUnivTyVars dc
    substitution = F.mkSortSubst (zip (F.symbol <$> variables) (F.FVar <$> [-1, -2 ..]))

tyConFTyCon :: TCEmb TyCon -> TyCon -> [Sort] -> Sort
-- ignore the nat arguments of the Any types, see test/pos/T2535A.hs
-- tyConFTyCon _ c _ | Ghc.zonkAnyTyCon  == c = FObj (symbol c)
tyConFTyCon tce c ts =
  case tceLookup c tce of
    Just (t, WithArgs) ->
      -- Templates use the constructor's own formal coordinates, never a
      -- caller's free variables. Query-local carriers are fully applied.
      F.sortSubst (F.mkSortSubst (zip (F.symbol <$> Ghc.tyConTyVars c) ts)) t
    Just (t, NoArgs)   -> fApp t ts
    Nothing            -> fApp (fTyconSort niTc) ts
  where
    niTc             = symbolNumInfoFTyCon (dummyLoc $ tyConName c) (isNumCls c) (isFracCls c)

tyVarSort :: TyVar -> Sort
tyVarSort = FObj . symbol

typeUniqueSymbol :: Type -> Symbol
typeUniqueSymbol = symbol . GM.typeUniqueString

typeSortForAll :: TCEmb TyCon -> Type -> Sort
typeSortForAll tce τ  = F.notracepp ("typeSortForall " ++ showpp τ) $ genSort sbody
  where
    sbody             = typeSort tce tbody
    genSort t         = foldl' (flip FAbs) (sortSubst su t) [i..n+i-1]
    (as, tbody)       = F.notracepp ("splitForallTys" ++ GM.showPpr τ) (splitForAllTyCoVars τ)
    su                = M.fromList $ zip sas (FVar <$>  [i..])
    sas               = symbol <$> as
    n                 = length as
    i                 = sortAbs sbody + 1

-- RJ: why not make this the Symbolic instance?
tyConName :: TyCon -> Symbol
tyConName c
  | listTyCon == c    = listConName
  | Ghc.isTupleTyCon c = symbol $ "Tuple" ++ show (tyConArity c)
  | otherwise         = symbol c

typeSortFun :: TCEmb TyCon -> Type -> Sort
typeSortFun tce t = mkFFunc 0 sos
  where
    sos           = typeSort tce <$> τs
    τs            = grabArgs [] t

grabArgs :: [Type] -> Type -> [Type]
grabArgs τs (FunTy _ _ τ1 τ2) =
    grabArgs (τ1 : τs) τ2
grabArgs τs τ =
    reverse (τ : τs)

expandProductType :: (PPrint r, IsReft r, SubsTy RTyVar (RType RTyCon RTyVar NoReft) r,
                      ReftBind r ~ Symbol, ReftVar r ~ Symbol, Variable r ~ Symbol)
                  => Var -> RType RTyCon RTyVar r -> RType RTyCon RTyVar r
expandProductType x t
  | isTrivial'      = t
  | otherwise       = fromRTypeRep $ trep {ty_binds = xs', ty_info=is', ty_args = ts', ty_refts = rs'}
     where
      isTrivial'    = ofType (varType x) == toRSort t
      τs            = map irrelevantMult $ fst $ splitFunTys $ snd $ splitForAllTyCoVars $ toType False t
      trep          = toRTypeRep t
      (xs',is',ts',rs') = unzip4 $ concatMap mkProductTy $ zip5 τs (ty_binds trep) (ty_info trep) (ty_args trep) (ty_refts trep)

-- splitFunTys :: Type -> ([Type], Type)

data DataConAppContext
  = DataConAppContext
  { dcac_dc      :: !DataCon
  , dcac_tys     :: ![Type]
  , dcac_arg_tys :: ![(Type, StrictnessMark)]
  , dcac_co      :: !Coercion
  }

mkProductTy :: forall t r. (IsReft t, IsReft r)
            => (Type, Symbol, RFInfo, RType RTyCon RTyVar r, t)
            -> [(Symbol, RFInfo, RType RTyCon RTyVar r, t)]
mkProductTy (τ, x, i, t, r) = maybe [(x, i, t, r)] f (deepSplitProductType menv τ)
  where
    f    :: DataConAppContext -> [(Symbol, RFInfo, RType RTyCon RTyVar r, t)]
    f    DataConAppContext{..} = map ((dummySymbol, defRFInfo, , trueReft) . ofType . fst) dcac_arg_tys
    menv = (emptyFamInstEnv, emptyFamInstEnv)

-- Copied from GHC 9.0.2.
orElse :: Maybe a -> a -> a
orElse = flip fromMaybe

-- Copied from GHC 9.0.2.
deepSplitProductType :: FamInstEnvs -> Type -> Maybe DataConAppContext
-- If    deepSplitProductType_maybe ty = Just (dc, tys, arg_tys, co)
-- then  dc @ tys (args::arg_tys) :: rep_ty
--       co :: ty ~ rep_ty
-- Why do we return the strictness of the data-con arguments?
-- Answer: see Note [Record evaluated-ness in worker/wrapper]
deepSplitProductType fam_envs ty
  | let Reduction co ty1 = topNormaliseType_maybe fam_envs ty
                    `orElse` Reduction (mkRepReflCo ty) ty
  , Just (tc, tc_args) <- splitTyConApp_maybe ty1
  , Just con <- tyConSingleDataCon_maybe tc
  , let arg_tys = dataConInstArgTys con tc_args
        strict_marks = dataConRepStrictness con
  = Just DataConAppContext { dcac_dc = con
                           , dcac_tys = tc_args
                           , dcac_arg_tys = zip (map irrelevantMult arg_tys) strict_marks
                           , dcac_co = co }

deepSplitProductType _ _ = Nothing


-----------------------------------------------------------------------------------------
-- | Binders generated by class predicates, typically for constraining tyvars (e.g. FNum)
-----------------------------------------------------------------------------------------
classBinds :: TCEmb TyCon -> SpecType -> [(Symbol, SortedReft)]
classBinds _ (RApp c ts _ _)
  | isFracCls c
  = [(symbol a, trueSortedReft FFrac) | (RVar a _) <- ts]
  | isNumCls c
  = [(symbol a, trueSortedReft FNum) | (RVar a _) <- ts]
classBinds emb (RApp c [_, _, RVar a _, t] _ _)
  | isEqual c
  = [(symbol a, rTypeSortedReft emb t)]
classBinds  emb ty@(RApp c [_, RVar a _, t] _ _)
  | isEqualityConstr ty
  = [(symbol a, rTypeSortedReft emb t)]
  | otherwise
  = notracepp ("CLASSBINDS-0: " ++ showpp c) []
classBinds _ t
  = notracepp ("CLASSBINDS-1: " ++ showpp (toType False t, isEqualityConstr t)) []

isEqualityConstr :: SpecType -> Bool
isEqualityConstr (toType False -> ty) = Ghc.isEqPred ty || Ghc.isEqClassPred ty

--------------------------------------------------------------------------------
-- | Termination Predicates ----------------------------------------------------
--------------------------------------------------------------------------------

makeNumEnv :: (Foldable t, TyConable c) => t (RType c b t1) -> [b]
makeNumEnv = concatMap go
  where
    go (RApp c ts _ _) | isNumCls c || isFracCls c = [ a | (RVar a _) <- ts]
    go _ = []

isDecreasing :: S.HashSet TyCon -> [RTyVar] -> SpecType -> Bool
isDecreasing autoenv  _ (RApp c _ _ _)
  =  isJust (sizeFunction (rtc_info c)) -- user specified size or
  || isSizeable autoenv tc
  where tc = rtc_tc c
isDecreasing _ cenv (RVar v _)
  = v `elem` cenv
isDecreasing _ _ _
  = False

isSizeable  :: S.HashSet TyCon -> TyCon -> Bool
isSizeable autoenv tc = S.member tc autoenv --   Ghc.isAlgTyCon tc -- && Ghc.isRecursiveTyCon tc

mkDecrFun :: Maybe F.LocSymbol -> S.HashSet TyCon -> RType RTyCon t t1 -> Symbol -> Expr
mkDecrFun sizeMeasure autoenv (RApp c _ _ _)
  | Just f <- szFun <$> sizeFunction (rtc_info c)
  = f
  | isSizeable autoenv $ rtc_tc c
  = \v -> F.mkEApp (fromMaybe (panic Nothing "Missing or ambiguous autosize measure declaration") sizeMeasure) [F.EVar v]
mkDecrFun _ _ (RVar _ _)
  = EVar
mkDecrFun _ _ _
  = panic Nothing "RefType.mkDecrFun called on invalid input"

makeLexRefa :: [Located Expr] -> [Located Expr] -> UReft
makeLexRefa es' es = uTop $ Reft (vv', PIff (EVar vv') $ pOr rs)
  where
    rs  = makeLexReft [] [] (val <$> es) (val <$> es')
    vv' = "vvRec"

makeLexReft :: [(Expr, Expr)] -> [Expr] -> [Expr] -> [Expr] -> [Expr]
makeLexReft _ acc [] []
  = acc
makeLexReft old acc (e:es) (e':es')
  = makeLexReft ((e,e'):old) (r:acc) es es'
  where
    r    = pAnd $   PAtom Lt e' e
                :   PAtom Ge e' zero
                :  [PAtom Eq o' o    | (o,o') <- old]
                ++ [PAtom Ge o' zero | (_,o') <- old]
    zero = ECon $ I 0
makeLexReft _ _ _ _
  = panic Nothing "RefType.makeLexReft on invalid input"

--------------------------------------------------------------------------------
mkTyConInfo :: TyCon -> VarianceInfo -> VarianceInfo -> Maybe SizeFun -> TyConInfo
mkTyConInfo c userTv userPv f = TyConInfo tcTv userPv f
  where
    tcTv                      = if null userTv then defTv else userTv
    defTv = M.findWithDefault [] c (makeTyConVariances M.empty M.empty [c])


-------------------------------------------------------------------------------
-- | tyVarsPosition t returns the type variables appearing
-- | (in positive positions, in negative positions, in undetermined positions)
-- | undetermined positions are due to type constructors and type application
-------------------------------------------------------------------------------
tyVarsPosition :: RType RTyCon tv r -> Positions tv
tyVarsPosition = go (Just True)
  where
    go p (RVar t _)         = report p t
    go p (RFun _ _ t1 t2 _) = go (flip' p) t1 <> go p t2
    go p (RAllT _ t _)      = go p t
    go p (RAllP _ t)        = go p t
    go p (RApp c ts _ _)    = mconcat (zipWith go (getPosition p <$> varianceTyArgs (rtc_info c)) ts)
    go p (REx _ t1 t2)      = go p t1 <> go p t2
    go _ (RLit _)           = mempty
    go _ (RExprArg _)       = mempty
    go p (RAppTy t1 t2 _)   = go p t1 <> go p t2
    go p (RRTy _ _ _ t)     = go p t
    go _ (RHole _)          = mempty

    getPosition :: Maybe Bool -> Variance -> Maybe Bool
    getPosition b Contravariant = not <$> b
    getPosition b _             = b

    report (Just True)  v = Pos [v] []  []
    report (Just False) v = Pos []  [v] []
    report Nothing v      = Pos []  []  [v]
    flip' = fmap not

data Positions a = Pos {ppos :: [a], pneg :: [a], punknown :: [a]}

instance Monoid (Positions a) where
  mempty = Pos [] [] []
instance Semigroup (Positions a) where
  (Pos x1 x2 x3) <> (Pos y1 y2 y3) = Pos (x1 ++ y1) (x2 ++ y2) (x3 ++ y3)
