-- | A type's positivity verdict must not depend on which module is being
--   compiled. From here `[]` is two levels out, so it misses the variance memo
--   table; a miss used to default to `Bivariant`, which reported
--   "Negative occurence of PositivityLib.T" -- against a module that is not the
--   compilation unit, for a type that is positive.
module PositivityImport where

import PositivityLib (T)

data W = W T
