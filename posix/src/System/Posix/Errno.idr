module System.Posix.Errno

import Data.C.Integer
import Data.Finite
import Data.Maybe
import Data.SortedMap
import public System.Posix.Errno.Type

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

export %inline
Interpolation Errno where
  interpolate = errorText

%default total
codeMap : SortedMap Bits32 Errno
codeMap = SortedMap.fromList $ map (\x => (errorCode x, x)) values

||| Convert an error code to the corresponding `Errno`.
|||
||| This returns `EOTHER` in case `x` is none of the predefined error
||| codes.
export
fromCode : Bits32 -> Errno
fromCode x = fromMaybe EOTHER (lookup x codeMap)

export %inline
fromNeg : Neg n => Cast n Bits32 => n -> Errno
fromNeg = fromCode . cast . negate

export %inline
negErr : Neg n => Cast n Bits32 => n -> Either Errno a
negErr x = Left (fromNeg x)

export %inline
toSize : PrimIO SsizeT -> IO (Either Errno Bits32)
toSize act =
  fromPrim $ \w =>
    let MkIORes r w := act w
     in case r < 0 of
          True  => MkIORes (negErr r) w
          False => MkIORes (Right $ cast r) w

export %inline
toUnit : PrimIO CInt -> IO (Either Errno ())
toUnit act =
  fromPrim $ \w =>
    let MkIORes r w := act w
     in case r < 0 of
          True  => MkIORes (negErr r) w
          False => MkIORes (Right ()) w

export %inline
toRes : IO a -> PrimIO CInt -> IO (Either Errno a)
toRes wrap act =
  toUnit act >>= \case
    Right () => Right <$> wrap
    Left x   => pure (Left x)

export %inline
toVal : (CInt -> a) -> PrimIO CInt -> IO (Either Errno a)
toVal wrap act =
  fromPrim $ \w =>
    let MkIORes r w := act w
     in case r < 0 of
          True  => MkIORes (negErr r) w
          False => MkIORes (Right $ wrap r) w

export %inline
primMap : (a -> b) -> PrimIO a -> PrimIO b
primMap f act w = let MkIORes v w := act w in MkIORes (f v) w
