module System.Posix.Time

import Data.C.Ptr

import public Data.C.Integer
import public System.Posix.Time.Types
import public System.Clock

%default total

--------------------------------------------------------------------------------
-- STimespec
--------------------------------------------------------------------------------

%foreign "C:get_tv_sec, posix-idris"
prim__get_tv_sec: AnyPtr -> PrimIO TimeT

%foreign "C:get_tv_nsec, posix-idris"
prim__get_tv_nsec: AnyPtr -> PrimIO NsecT

%foreign "C:set_tv_sec, posix-idris"
prim__set_tv_sec: AnyPtr -> TimeT -> PrimIO ()

%foreign "C:set_tv_nsec, posix-idris"
prim__set_tv_nsec: AnyPtr -> NsecT -> PrimIO ()

||| A wrapper around a `struct timespec` pointer.
export
record STimespec where
  constructor TS
  ptr : AnyPtr

export %inline
Struct STimespec where
  wrap   = TS
  unwrap = ptr

public export %inline
SizeOf STimespec where
  sizeof_ = timespec_size

||| Reads the `tv_sec` field of a `timespec` pointer.
export %inline
sec : STimespec -> PrimIO TimeT
sec (TS p) = prim__get_tv_sec p

||| Reads the `tv_nsec` field of a `timespec` pointer.
export %inline
nsec : STimespec -> PrimIO NsecT
nsec (TS p) = prim__get_tv_nsec p

||| Sets the `tv_sec` field of a `timespec` pointer.
export %inline
setSec : STimespec -> TimeT -> PrimIO ()
setSec (TS p) t = prim__set_tv_sec p t

||| Sets the `tv_nsec` field of a `timespec` pointer.
export %inline
setNsec : STimespec -> NsecT -> PrimIO ()
setNsec (TS p) t = prim__set_tv_nsec p t

||| Convert a `STimespec` to a `Clock t`
export %inline
toClock : {t : _} -> STimespec -> PrimIO (Clock t)
toClock ts w =
  let MkIORes x0 w := sec ts w
      MkIORes x1 w := nsec ts w
   in MkIORes (MkClock (cast x0) (cast x1)) w
