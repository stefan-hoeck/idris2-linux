module System.Posix.Errno

import Data.C.Integer
import Data.Finite
import Data.Maybe
import Data.SortedMap
import public System.Posix.Errno.Type

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

public export %inline
toBool : Bits8 -> Bool
toBool 0 = False
toBool _ = True

export %inline
Interpolation Errno where
  interpolate x = "\{errorText x} (\{errorName x})"

export %inline
fromNeg : Neg n => Cast n Bits32 => n -> Errno
fromNeg = EN . cast . negate

public export
interface HasIO io => ErrIO io where
  error : Errno -> io a

parameters {auto err : ErrIO io}
  export %inline
  toSize : PrimIO SsizeT -> io Bits32
  toSize act = do
    r <- primIO act
    if r < 0 then error (fromNeg r) else pure (cast r)

  export %inline
  toUnit : PrimIO CInt -> io ()
  toUnit act = do
    r <- primIO act
    if r < 0 then error (fromNeg r) else pure ()

  export %inline
  toPidT : PrimIO PidT -> io PidT
  toPidT act = do
    r <- primIO act
    if r < 0 then error (fromNeg r) else pure r

  export %inline
  posToUnit : PrimIO Bits32 -> io ()
  posToUnit act = do
    0 <- primIO act | x => error (EN x)
    pure ()

  export %inline
  toRes : io a -> PrimIO CInt -> io a
  toRes wrap act = toUnit act >> wrap

  export %inline
  toVal : (CInt -> a) -> PrimIO CInt -> io a
  toVal wrap act = do
    r <- primIO act
    if r < 0 then error (fromNeg r) else pure (wrap r)

export %inline
primMap : HasIO io => (a -> b) -> PrimIO a -> io b
primMap f act = primIO $ \w => let MkIORes v w := act w in MkIORes (f v) w
