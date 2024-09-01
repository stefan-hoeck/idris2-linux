module System.Linux.Error

import Data.C.Integer
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

export %inline
toRes : (toErr : Lazy (Error -> e)) -> IO a -> PrimIO CInt -> IO (Either e a)
toRes toErr res act =
  fromPrim $ \w =>
    let MkIORes r w := act w
     in case r < 0 of
          True  => MkIORes (resErr r toErr) w
          False => toPrim (Right <$> res) w

export %inline
toFD : (toErr : Lazy (Error -> e)) -> PrimIO CInt -> IO (Either e Bits32)
toFD toErr act =
  fromPrim $ \w =>
    let MkIORes r w := act w
     in case r < 0 of
          True  => MkIORes (resErr r toErr) w
          False => MkIORes (Right $ cast r) w

export %inline
toSize : (toErr : Lazy (Error -> e)) -> PrimIO SsizeT -> IO (Either e Bits32)
toSize toErr act =
  fromPrim $ \w =>
    let MkIORes r w := act w
     in case r < 0 of
          True  => MkIORes (resErr r toErr) w
          False => MkIORes (Right $ cast r) w

export %inline
toUnit : (toErr : Lazy (Error -> e)) -> PrimIO CInt -> IO (Either e ())
toUnit toErr act =
  fromPrim $ \w =>
    let MkIORes r w := act w
     in case r < 0 of
          True  => MkIORes (resErr r toErr) w
          False => MkIORes (Right ()) w
