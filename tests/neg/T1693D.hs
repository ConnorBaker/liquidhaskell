{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | The negative half of `T1693C`: the same dictionary-function shape, with a
--   FALSE claim on the written `mempty` -- `SelfContainment 0 0` is claimed to
--   carry `selfContainmentAmbiguous == 1`.
--
--   The expectation names the error rather than accepting any. Before
--   `getExprFun` was total this module did not fail with a type mismatch; it
--   panicked during constraint generation and never reached the false claim, so
--   `--expect-any-error` would be discharged by the very defect `T1693C` exists
--   to catch. Only a real refutation of the `mempty` spec satisfies this.
--
--   https://github.com/ucsd-progsys/liquidhaskell/issues/1693
module T1693D where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

newtype Pointwise k v = Pointwise (Map k v)

instance (Ord k, Semigroup v) => Semigroup (Pointwise k v) where
  Pointwise a <> Pointwise b = Pointwise (Map.unionWith (<>) a b)

instance (Ord k, Semigroup v) => Monoid (Pointwise k v) where
  mempty = Pointwise Map.empty

data SelfContainment = SelfContainment
  { selfContainmentAmbiguous  :: Int
  , selfContainmentUnresolved :: Int
  }

{-@ data SelfContainment = SelfContainment
      { selfContainmentAmbiguous  :: Nat
      , selfContainmentUnresolved :: Nat
      }
  @-}

{-@ instance Semigroup SelfContainment where
      <> :: left:SelfContainment -> right:SelfContainment
         -> { v : SelfContainment
            | selfContainmentAmbiguous  v == selfContainmentAmbiguous  left + selfContainmentAmbiguous  right
           && selfContainmentUnresolved v == selfContainmentUnresolved left + selfContainmentUnresolved right }
  @-}
instance Semigroup SelfContainment where
  SelfContainment a1 u1 <> SelfContainment a2 u2 = SelfContainment (a1 + a2) (u1 + u2)

-- FALSE: 'mempty' is 'SelfContainment 0 0', not ambiguous-count 1.
{-@ instance Monoid SelfContainment where
      mempty :: { v : SelfContainment | selfContainmentAmbiguous v == 1 && selfContainmentUnresolved v == 0 }
  @-}
instance Monoid SelfContainment where
  mempty = SelfContainment 0 0

{-@ tally :: Ord key => Map key Nat -> Pointwise key SelfContainment @-}
tally :: Ord key => Map key Int -> Pointwise key SelfContainment
tally = Map.foldMapWithKey (\k n -> Pointwise (Map.singleton k (SelfContainment n 0)))
