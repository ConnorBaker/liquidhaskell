{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingVia        #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-} -- TODO(#1918): Only needed for GHC <9.0.1.
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Haskell.Liquid.Types.Variance (
  Variance(..), VarianceInfo, makeTyConVariances, flipVariance
  ) where

import Prelude hiding (error)
import Control.DeepSeq
import Data.Data     hiding (TyCon)
import GHC.Generics
import Data.Binary
import Data.Hashable
import Text.PrettyPrint.HughesPJ

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet            as S
import GHC.Core.Type (coreView, tyConsOfType)
import GHC.Types.Unique.Set (nonDetEltsUniqSet)

import qualified Language.Fixpoint.Types as F

import qualified Language.Haskell.Liquid.GHC.Misc as GM
import           Liquid.GHC.API        as Ghc hiding (Binary, text)

type VarianceInfo = [Variance]

data Variance = Invariant | Bivariant | Contravariant | Covariant
              deriving (Eq, Data, Show, Generic)
              deriving Hashable via Generically Variance

flipVariance :: Variance -> Variance
flipVariance Invariant     = Invariant
flipVariance Bivariant     = Bivariant
flipVariance Contravariant = Covariant
flipVariance Covariant     = Contravariant

instance Semigroup Variance where
  Invariant <> _ = Invariant
  _ <> Invariant = Invariant
  Bivariant     <> _         = Bivariant
  _             <> Bivariant = Bivariant
  Covariant     <> v         = v
  Contravariant <> v         = flipVariance v

instance Monoid Variance where
  mempty = Covariant

instance Binary Variance
instance NFData Variance
instance F.PPrint Variance where
  pprintTidy _ = text . show

-- External interfaces are fixed boundaries; local annotations are only lower
-- bounds, so they cannot erase an occurrence found in the constructor fields.
makeTyConVariances :: M.HashMap TyCon VarianceInfo -> M.HashMap TyCon VarianceInfo -> [TyCon] -> M.HashMap TyCon VarianceInfo
makeTyConVariances external declared roots = fixedPoint initial
  where
    declarations = collect M.empty roots
    initial = M.union external $ M.mapWithKey (\c _ -> replicate (length (GM.tyConTyVarsDef c)) Invariant) declarations

    -- Each parameter accumulates a subset of {positive, negative}. Starting
    -- with no occurrences gives a finite least fixed point, including changed
    -- arguments of recursive applications. Variance's Semigroup is not union.
    fixedPoint variances
      | next == variances = variances
      | otherwise = fixedPoint next
      where
        next = M.union external $ M.mapWithKey step declarations
        step c bodies = zipWith union (varianceOf variances c bodies) (M.findWithDefault [] c declared ++ repeat Invariant)

    union Invariant v = v
    union v Invariant = v
    union v w | v == w = v
    union _ _ = Bivariant

    collect seen [] = seen
    collect seen (c : cs)
      | M.member c seen || M.member c external = collect seen cs
      | otherwise = collect (M.insert c bodies seen) (dependencies ++ cs)
      where
        bodies = case Ghc.synTyConRhs_maybe c of
          Just rhs -> Just [rhs]
          Nothing -> concatMap fields <$> Ghc.tyConDataCons_maybe c
        dependencies = maybe [] (concatMap (nonDetEltsUniqSet . tyConsOfType)) bodies
        -- Constructor universals correspond positionally to the parent's
        -- parameters, but need not have the same names or native identities.
        fields dc = map (Ghc.substTyWith (Ghc.dataConUnivTyVars dc) (Ghc.mkTyVarTys (Ghc.tyConTyVars c)) . irrelevantMult) (Ghc.dataConOrigArgTys dc)

    varianceOf _ c Nothing = replicate (length (GM.tyConTyVarsDef c)) Bivariant
    varianceOf variances c (Just bodies) = map (varSignToVariance signs) (GM.tyConTyVarsDef c)
      where
        signs = S.unions (map (go variances True) bodies)

    varSignToVariance signs v = case (S.member (v, True) signs, S.member (v, False) signs) of
      (False, False) -> Invariant
      (True, False) -> Covariant
      (False, True) -> Contravariant
      (True, True) -> Bivariant

    go variances pos (FunTy _ _ t1 t2) = go variances (not pos) t1 `S.union` go variances pos t2
    go variances pos (ForAllTy _ t) = go variances pos t
    go _ pos (TyVarTy v) = S.singleton (v, pos)
    go variances pos (AppTy t1 t2) = go variances pos t1 `S.union` goTyConApp variances pos Bivariant t2
    go variances pos t@(TyConApp c ts)
      | Just vs <- M.lookup c variances = S.unions $ zipWith (goTyConApp variances pos) (vs ++ repeat Bivariant) ts
      | Just t' <- coreView t = go variances pos t'
      | otherwise = S.unions $ map (goTyConApp variances pos Bivariant) ts
    go _ _ (LitTy _) = S.empty
    go _ _ (CoercionTy _) = S.empty
    go variances pos (CastTy t _) = go variances pos t

    goTyConApp _ _ Invariant _ = S.empty
    goTyConApp variances pos Bivariant t = go variances pos t `S.union` go variances (not pos) t
    goTyConApp variances pos Covariant t = go variances pos t
    goTyConApp variances pos Contravariant t = go variances (not pos) t
