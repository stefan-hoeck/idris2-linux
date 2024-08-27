module System.Linux.Error

import Debug.Trace
import Data.Finite
import Data.Maybe
import Data.SortedMap
import public System.Linux.Error.Type

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

export %inline
Interpolation Error where
  interpolate = errorText

%default total
codeMap : SortedMap Bits32 Error
codeMap = SortedMap.fromList $ map (\x => (errorCode x, x)) values

||| Convert an error code to the corresponding `Error`.
|||
||| This returns `EOTHER` in case `x` is none of the predefined error
||| codes.
export
fromCode : Bits32 -> Error
fromCode x = fromMaybe EOTHER (lookup x codeMap)

export %inline
fromRes : Neg n => Cast n Bits32 => n -> Error
fromRes = fromCode . cast . negate

export %inline
resErr : Neg n => Cast n Bits32 => n -> (Error -> e) -> Either e a
resErr x f = Left (f $ fromRes x)
