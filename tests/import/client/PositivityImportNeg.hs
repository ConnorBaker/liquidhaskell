{-@ LIQUID "--expect-error-containing=Negative occurence" @-}

-- | The variance fallback must not weaken the check. `repeat Bivariant` was
--   the maximally rejecting default -- it puts the argument in both posOcc and
--   negOcc -- so replacing it with a computed value can only turn a rejection
--   into an acceptance. A real negative occurrence, through an imported
--   contravariant container, must still be reported.
module PositivityImportNeg where

import PositivityLib (Pred)

data Bad = MkBad (Pred Bad)
