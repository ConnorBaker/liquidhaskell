-- | A third arming shape for #1693, distinct from `T1693A`'s. There the
--   refined `Monoid` dictionary was the ARGUMENT of a class method (`foldMap`,
--   with the `Foldable` dictionary in front of it). Here it is the argument of
--   a dictionary FUNCTION: `Pointwise`'s `Monoid` instance takes an `Ord k`
--   witness before the refined `Semigroup v` one, so the dictionary that
--   `foldMapWithKey` demands is built as
--
--   > $fMonoidPointwise @key @SelfContainment $dOrd $fSemigroupSelfContainment
--
--   and `consEApp`, having found the refined `Semigroup` dictionary in argument
--   position, asked `getExprFun` for the function part -- whose outermost
--   application carries a VALUE argument (`$dOrd`), not a type. `getExprFun` saw
--   through type applications only, so this reached its `panic` equation with
--   "getFunName on $fMonoidPointwise @key @SelfContainment $dOrd".
--
--   Two things are load-bearing. The `(Ord k, Semigroup v)` context order: with
--   `Semigroup v` first the refined dictionary is the inner argument and no
--   value argument intervenes. And the key being POLYMORPHIC: a closed
--   `Monoid (Pointwise Int SelfContainment)` is floated by GHC to a top-level
--   derived binder, which `consCBTop` trusts with a `trueTy` and never walks,
--   so that shape is unreachable under this group's flags and reaches the panic
--   only with `--check-derived`. A lambda-bound `$dOrd` keeps the application
--   local, where `consE` walks into it.
--
--   https://github.com/ucsd-progsys/liquidhaskell/issues/1693
module T1693C where

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

{-@ instance Monoid SelfContainment where
      mempty :: { v : SelfContainment | selfContainmentAmbiguous v == 0 && selfContainmentUnresolved v == 0 }
  @-}
instance Monoid SelfContainment where
  mempty = SelfContainment 0 0

{-@ tally :: Ord key => Map key Nat -> Pointwise key SelfContainment @-}
tally :: Ord key => Map key Int -> Pointwise key SelfContainment
tally = Map.foldMapWithKey (\k n -> Pointwise (Map.singleton k (SelfContainment n 0)))
