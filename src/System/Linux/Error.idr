module System.Linux.Error

import Data.Finite
import Data.Maybe
import Data.SortedMap
import public System.Linux.Error.Type

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_errno, linux-idris"
prim__errno : PrimIO Bits32

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

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

||| Reads the `errno` variable and converts it to an `Error`.
export %inline
lastError : IO Error
lastError = map fromCode (fromPrim prim__errno)
