module System.Posix.Timer

import Data.C.Ptr

import public Data.C.Integer
import public System.Posix.Errno
import public System.Posix.Timer.Types

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:clock, posix-idris"
prim__clock : PrimIO ClockT

%foreign "C:alarm, posix-idris"
prim__alarm : UInt -> PrimIO UInt

%foreign "C:li_timeval, posix-idris"
prim__timeval : TimeT -> SusecondsT -> PrimIO AnyPtr

%foreign "C:li_itimerval, posix-idris"
prim__itimerval : TimeT -> SusecondsT -> TimeT -> SusecondsT -> PrimIO AnyPtr

%foreign "C:li_tv_sec, posix-idris"
prim__tv_sec : AnyPtr -> PrimIO TimeT

%foreign "C:li_tv_usec, posix-idris"
prim__tv_usec : AnyPtr -> PrimIO SusecondsT

%foreign "C:li_it_interval, posix-idris"
prim__it_interval : AnyPtr -> PrimIO AnyPtr

%foreign "C:li_it_value, posix-idris"
prim__it_value : AnyPtr -> PrimIO AnyPtr

%foreign "C:li_setitimer, posix-idris"
prim__setitimer : Bits8 -> AnyPtr -> AnyPtr -> PrimIO CInt

%foreign "C:li_setitimer1, posix-idris"
prim__setitimer1 : Bits8 -> AnyPtr -> PrimIO CInt

%foreign "C:li_getitimer, posix-idris"
prim__getitimer : Bits8 -> AnyPtr -> PrimIO CInt

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Returns an approximation of processor time used by the program.
|||
||| Type `ClockT` measures time with a granularity of
||| `CLOCKS_PER_SEC`.
export %inline
clock : HasIO io => io ClockT
clock = primIO prim__clock

||| A wrapper around a `struct timeval` pointer.
export
record Timeval where
  constructor TV
  ptr : AnyPtr

||| Allocates a `Timeval` pointer.
|||
||| The allocated memory must be freed via `freeTimeval`.
export %inline
allocTimeval : HasIO io => io Timeval
allocTimeval = primIO $ MkIORes (TV $ prim__malloc timeval_size)

||| Frees the memory allocated for a `Timeval` pointer.
export %inline
freeTimeval : HasIO io => Timeval -> io ()
freeTimeval (TV p) = primIO $ prim__free p

||| Creates and sets the fields of a `Timeval` pointer.
|||
||| The allocated memory must be freed via `freeTimeval`.
export %inline
timeval : HasIO io => TimeT -> SusecondsT -> io Timeval
timeval s u =
  primIO $ \w =>
    let MkIORes p w := prim__timeval s u w
     in MkIORes (TV p) w

||| Returns the `tv_sec` field of a `timeval` pointer.
export %inline
sec : HasIO io => Timeval -> io TimeT
sec (TV p) = primIO $ prim__tv_sec p

||| Returns the `tv_usec` field of a `timeval` pointer.
export %inline
usec : HasIO io => Timeval -> io SusecondsT
usec (TV p) = primIO $ prim__tv_usec p

||| A wrapper around a `struct itimerval` pointer.
export
record Itimerval where
  constructor ITV
  ptr : AnyPtr

||| Allocates an `Itimerval` pointer.
|||
||| The allocated memory must be freed via `freeItimerval`.
export %inline
allocItimerval : HasIO io => io Itimerval
allocItimerval = primIO $ MkIORes (ITV $ prim__malloc itimerval_size)

||| Frees the memory allocated for a `Itimerval` pointer.
export %inline
freeItimerval : HasIO io => Itimerval -> io ()
freeItimerval (ITV p) = primIO $ prim__free p

||| Creates and sets the fields of a `Itimerval` pointer.
|||
||| The allocated memory must be freed via `freeItimerval`.
export %inline
itimerval :
     {auto has     : HasIO io}
  -> (secInterval  : TimeT)
  -> (usecInterval : SusecondsT)
  -> (secValue     : TimeT)
  -> (usecValue    : SusecondsT)
  -> io Itimerval
itimerval si ui sv uv =
  primIO $ \w =>
    let MkIORes p w := prim__itimerval si ui sv uv w
     in MkIORes (ITV p) w

||| Returns a pointer to the `it_interval` field of a `itimerval` pointer.
export %inline
interval : HasIO io => Itimerval -> io Timeval
interval (ITV p) =
  primIO $ \w => let MkIORes p2 w := prim__it_interval p w in MkIORes (TV p2) w

||| Returns a pointer to the `it_interval` field of a `itimerval` pointer.
export %inline
value : HasIO io => Itimerval -> io Timeval
value (ITV p) =
  primIO $ \w => let MkIORes p2 w := prim__it_value p w in MkIORes (TV p2) w

||| This sets `new` as the new timer and places the current timer for
||| `Which` in `old`.
|||
||| Depending on `Which`, the timer will use a different clock and
||| will (possibly repeatedly) raise a different kind signal:
|||
||| * ITIMER_REAL: Counts down in real (i.e. wall clock) time
|||   and raises SIGALRM
||| * ITIMER_VIRTUAL: Counts down in process virtual time
|||   (i.e. user-mode CPU time) and raises SIGVTALRM
||| * ITIMER_PROF: Counts down in process time
|||   (i.e. the sum of kernel-mode and user-mode CPU time) and raises SIGPROF
export %inline
setitimer : Which -> (new,old : Itimerval) -> IO (Either Errno ())
setitimer w (ITV n) (ITV o) = toUnit $ prim__setitimer (whichCode w) n o

||| Like `setitimer` but does not store the old timer in a pointer.
export %inline
setitimer' : Which -> (new : Itimerval) -> IO (Either Errno ())
setitimer' w (ITV n) = toUnit $ prim__setitimer1 (whichCode w) n

||| Writes the currently set timer for `Which` into `old.
export %inline
getitimer : Which -> (old : Itimerval) -> IO (Either Errno ())
getitimer w (ITV o) = toUnit $ prim__getitimer (whichCode w) o

||| A very basic version of `setitimer` that raises `SIGALRM`
||| after the given number of seconds.
|||
||| The returned value is the remaining number of seconds on any
||| previously set timer. The timer can be disabled by setting
||| this to zero.
export %inline
alarm : HasIO io => UInt -> io UInt
alarm s = primIO $ prim__alarm s
