module System.Posix.Time

import Data.C.Ptr

import public Data.C.Integer
import public System.Posix.Time.Types
import public System.Clock

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:get_tv_sec, posix-idris"
prim__get_tv_sec: AnyPtr -> PrimIO TimeT

%foreign "C:get_tv_nsec, posix-idris"
prim__get_tv_nsec: AnyPtr -> PrimIO NsecT

%foreign "C:set_tv_sec, posix-idris"
prim__set_tv_sec: AnyPtr -> TimeT -> PrimIO ()

%foreign "C:set_tv_nsec, posix-idris"
prim__set_tv_nsec: AnyPtr -> NsecT -> PrimIO ()

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| A wrapper around a `struct timespec` pointer.
export
record Timespec where
  constructor TS
  ptr : AnyPtr

export %inline
Deref Timespec where
  deref = pure . TS

public export %inline
SizeOf Timespec where
  sizeof_ = cast timespec_size

||| Allocates a `Timespec` pointer.
|||
||| The allocated memory must be freed via `freeTimespec`.
export %inline
allocTimespec : HasIO io => io Timespec
allocTimespec = primIO $ MkIORes (TS $ prim__malloc timespec_size)

||| Frees the memory allocated for a `Timespec` pointer.
export %inline
freeTimespec : HasIO io => Timespec -> io ()
freeTimespec (TS p) = primIO $ prim__free p

||| Reads the `tv_sec` field of a `timespec` pointer.
export %inline
sec : HasIO io => Timespec -> io TimeT
sec (TS p) = primIO $ prim__get_tv_sec p

||| Reads the `tv_nsec` field of a `timespec` pointer.
export %inline
nsec : HasIO io => Timespec -> io NsecT
nsec (TS p) = primIO $ prim__get_tv_nsec p

||| Sets the `tv_sec` field of a `timespec` pointer.
export %inline
setSec : HasIO io => Timespec -> TimeT -> io ()
setSec (TS p) t = primIO $ prim__set_tv_sec p t

||| Sets the `tv_nsec` field of a `timespec` pointer.
export %inline
setNsec : HasIO io => Timespec -> NsecT -> io ()
setNsec (TS p) t = primIO $ prim__set_tv_nsec p t

||| Convert a `Timespec` to a `Clock t`
export %inline
toClock : HasIO io => {t : _} -> Timespec -> io (Clock t)
toClock ts = do
  x0 <- sec ts
  x1 <- nsec ts
  pure (MkClock (cast x0) (cast x1))
