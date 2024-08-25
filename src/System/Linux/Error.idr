module System.Linux.Error

import Data.Finite
import Data.Maybe
import Data.SortedMap
import public System.Linux.Error.Type

%default total
codeMap : SortedMap Bits32 Error
codeMap = SortedMap.fromList $ map (\x => (errorCode x, x)) values

export
fromCode : Bits32 -> Error
fromCode x = fromMaybe EOTHER (lookup x codeMap)
