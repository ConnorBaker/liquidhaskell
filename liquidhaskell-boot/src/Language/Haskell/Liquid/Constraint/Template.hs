{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE DeriveTraversable         #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Language.Haskell.Liquid.Constraint.Template (
  Template(..)
, unTemplate
, varTemplate
, addPostTemplate
, safeFromAsserted
, topSpecType
, derivedVar
, extenderWith
, extenderAfterBodyWith
, sourceCallableIdentity
, recursiveHypothesis
, recursiveCallable
) where

import           Prelude hiding (error)
import qualified Data.Foldable                                 as F
import qualified Data.Traversable                              as T
import qualified Data.HashSet                                  as S
import           Control.Monad.State ( gets )
import           Text.PrettyPrint.HughesPJ ( text, (<+>) )
import           GHC.Types.Var (Var)
import           GHC.Core (CoreExpr)
import           GHC.Core.Utils ( exprType )
import qualified Language.Fixpoint.Types                       as F
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.Specs
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Fresh (refreshArgs)
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Constraint.Env ( lookupREnv, (+=) )
import           Language.Haskell.Liquid.Constraint.Monad (addPost, addW)
import           Language.Haskell.Liquid.Constraint.Fresh (refreshArgsTop, freshTyExpr)
import           Language.Haskell.Liquid.Constraint.Init (defaultTopVars)
import qualified Language.Haskell.Liquid.Bare.Axiom as Axiom
import           Language.Haskell.Liquid.UX.Config

-- Template

data Template a
  = Asserted a
  | Assumed a
  | Internal a
  | Unknown
  deriving (Functor, F.Foldable, T.Traversable)

deriving instance (Show a) => (Show (Template a))

instance PPrint a => PPrint (Template a) where
  pprintTidy k (Asserted t) = text "Asserted" <+> pprintTidy k t
  pprintTidy k (Assumed  t) = text "Assumed"  <+> pprintTidy k t
  pprintTidy k (Internal t) = text "Internal" <+> pprintTidy k t
  pprintTidy _ Unknown      = text "Unknown"

unTemplate :: Template t -> t
unTemplate (Asserted t) = t
unTemplate (Assumed t)  = t
unTemplate (Internal t) = t
unTemplate _            = panic Nothing "Constraint.Template.unTemplate called on `Unknown`"

addPostTemplate :: CGEnv
                -> Template SpecType
                -> CG (Template SpecType)
addPostTemplate γ (Asserted t) = Asserted <$> addPost γ t
addPostTemplate γ (Assumed  t) = Assumed  <$> addPost γ t
addPostTemplate γ (Internal t) = Internal <$> addPost γ t
addPostTemplate _ Unknown      = return Unknown

safeFromAsserted :: [Char] -> Template t -> t
safeFromAsserted _   (Asserted t) = t
safeFromAsserted msg  _           = panic Nothing $ "safeFromAsserted:" ++ msg

-- | @varTemplate@ is only called with a `Just e` argument when the `e`
-- corresponds to the body of a @Rec@ binder.
varTemplate :: CGEnv -> (Var, Maybe CoreExpr) -> CG (Template SpecType)
varTemplate γ (x, eo) = varTemplate' γ (x, eo) >>= mapM (topSpecType x)

-- | @lazVarTemplate@ is like `varTemplate` but for binders that are *not*
--   termination checked and hence, the top-level refinement / KVar is
--   stripped out. e.g. see tests/neg/T743.hs
-- varTemplate :: CGEnv -> (Var, Maybe CoreExpr) -> CG (Template SpecType)
-- lazyVarTemplate γ (x, eo) = dbg <$> (topRTypeBase <$>) <$> varTemplate' γ (x, eo)
--   where
--    dbg   = traceShow ("LAZYVAR-TEMPLATE: " ++ show x)

varTemplate' :: CGEnv -> (Var, Maybe CoreExpr) -> CG (Template SpecType)
varTemplate' γ (x, eo)
  = case (eo, lookupREnv (F.symbol x) (grtys γ), lookupREnv (F.symbol x) (assms γ), lookupREnv (F.symbol x) (intys γ)) of
      (_, Just t, _, _) -> Asserted <$> refreshArgsTop (x, t)
      (_, _, _, Just t) -> Internal <$> refreshArgsTop (x, t)
      (_, _, Just t, _) -> Assumed  <$> refreshArgsTop (x, t)
      (Just e, _, _, _) -> do t <- freshTyExpr (typeclass (getConfig γ)) (RecBindE x) e (exprType e)
                              addW (WfC γ t)
                              Asserted <$> refreshArgsTop (x, t)
      (_,      _, _, _) -> return Unknown

-- | Only trusted generated bodies may discard their top-level checking goal.
topSpecType :: Var -> SpecType -> CG SpecType
topSpecType x t = do
  info <- gets ghcI
  return $ if derivedVar (giSrc info) x && not (checkDerived (getConfig info)) then topRTypeBase t else t

derivedVar :: TargetSrc -> Var -> Bool
derivedVar src x = S.member x (giDerVars src)

-- Pre-body hypotheses use the independently admitted callable, when present,
-- rather than treating an asserted checking target as an established result.
extenderWith :: F.Symbolic a => (SpecType -> SpecType) -> CGEnv -> (a, Template SpecType) -> CG CGEnv
extenderWith f γ (x, Asserted t)
  = case lookupREnv (F.symbol x) (assms γ) of
      Just t' -> γ += ("extender", F.symbol x, f t')
      _       -> γ += ("extender", F.symbol x, f t)
extenderWith f γ (x, Assumed t) =
    γ += ("extender", F.symbol x, f t)
extenderWith _ γ _ =
    return γ

-- Post-body extension carries the returned, postprocessed checking template.
-- The ordinary assumption selection above still governs pre-body hypotheses.
-- Original Assumed roles and rejected expected goals retain that trust/cut;
-- generating a body constraint never establishes their authored postcondition.
extenderAfterBodyWith :: (SpecType -> SpecType) -> CGEnv -> (Var, Template SpecType, Template SpecType) -> CG CGEnv
extenderAfterBodyWith f env (owner, original, checked)
    | F.symbol owner `S.member` S.map (F.symbol . F.val) (gsFail (gsTerm (giSpec (cgInfo env)))) =
        extenderWith publish env (owner, checked)
    | Assumed{} <- original = extenderWith publish env (owner, checked)
    | owner `elem` defaultTopVars (cgInfo env) = extenderWith publish env (owner, checked)
    | otherwise = case checked of
        Asserted ty -> env += ("checked body", F.symbol owner, publish ty)
        Internal ty -> env += ("checked internal body", F.symbol owner, publish ty)
        _ -> extenderWith publish env (owner, checked)
  where
    publish = f . sourceCallableIdentity (getConfig env) (gsSig (giSpec (cgInfo env))) owner

-- A registered source call names this same value's result. Decorating an
-- established callable preserves its input telescope and all proved results;
-- the registration supplies no independent result contract or body equation.
sourceCallableIdentity :: Config -> GhcSpecSig -> Var -> SpecType -> SpecType
sourceCallableIdentity cfg signatures owner ty
    | Just _ <- lookup owner (gsRefSigs signatures) =
        Axiom.aty (Axiom.addSingletonApp (typeclass cfg) (F.symbol owner) ty)
    | otherwise = ty

-- Structurally checked recursion retains its result induction hypotheses;
-- explicit no-termination mode uses the same interface interpretation.
-- A predicate on the function value itself has no such call premise: prove it
-- at the actual lambda before publishing it outside the recursive group.
-- Logical termination instead guards the complete source-prefix result in
-- Termination.addObligation before exposing any of its value predicates.
recursiveHypothesis :: SpecType -> SpecType
recursiveHypothesis (RAllT a t r) = topRTypeBase $ RAllT a (recursiveHypothesis t) r
recursiveHypothesis (RAllP p t) = RAllP p (recursiveHypothesis t)
recursiveHypothesis (REx x tx t) = REx x tx (recursiveHypothesis t)
recursiveHypothesis (RRTy xts r o t) = RRTy xts r o (recursiveHypothesis t)
recursiveHypothesis t@RFun{} = topRTypeBase t
recursiveHypothesis t = t

-- Expected-failure targets are goals, not induction hypotheses. Select their
-- independently admitted callable before adding any decrease obligation.
-- Other owners retain the existing recursive-contract interpretation.
recursiveCallable :: (F.Symbolic a) => CGEnv -> a -> SpecType -> CG SpecType
recursiveCallable γ owner target
  | F.symbol owner `S.member` S.map (F.symbol . F.val) (gsFail (gsTerm (giSpec (cgInfo γ))))
  , Just admitted <- lookupREnv (F.symbol owner) (assms γ) =
      refreshArgs admitted
  | otherwise =
      pure target
