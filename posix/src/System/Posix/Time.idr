module System.Posix.Time

import Data.C.Integer
import Data.C.Struct
import Derive.Prelude
import public System.Clock

%default total

export %foreign "C:calloc_timespec, posix-idris"
calloc_timespec: PrimIO AnyPtr

export %foreign "C:get_timespec_tv_sec, posix-idris"
get_timespec_tv_sec: AnyPtr -> PrimIO TimeT

export %foreign "C:get_timespec_tv_nsec, posix-idris"
get_timespec_tv_nsec: AnyPtr -> PrimIO NsecT

export
toClock : AnyPtr -> IO (Clock UTC)
toClock p = do
  x0 <- fromPrim $ get_timespec_tv_sec p
  x1 <- fromPrim $ get_timespec_tv_nsec p
  pure (MkClock (cast x0) (cast x1))