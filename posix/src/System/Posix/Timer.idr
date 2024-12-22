module System.Posix.Timer

import Data.C.Ptr

import Derive.Prelude

import public Data.C.Integer
import public System.Posix.Errno
import public System.Posix.Timer.Types
import public System.Posix.Time

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- STimeval
--------------------------------------------------------------------------------

%foreign "C:get_timeval_tv_sec, posix-idris"
get_timeval_tv_sec: AnyPtr -> PrimIO TimeT

%foreign "C:get_timeval_tv_usec, posix-idris"
get_timeval_tv_usec: AnyPtr -> PrimIO SusecondsT

%foreign "C:set_timeval_tv_sec, posix-idris"
set_timeval_tv_sec: AnyPtr -> TimeT -> PrimIO ()

%foreign "C:set_timeval_tv_usec, posix-idris"
set_timeval_tv_usec: AnyPtr -> SusecondsT -> PrimIO ()

%foreign "C:li_timeval, posix-idris"
prim__timeval : TimeT -> SusecondsT -> PrimIO AnyPtr

export
record STimeval where
  constructor STV
  ptr : AnyPtr

export %inline
Struct STimeval where
  wrap   = STV
  unwrap = ptr

export %inline
SizeOf STimeval where
  sizeof_ = timeval_size

export %inline
sec : STimeval -> PrimIO TimeT
sec s = get_timeval_tv_sec s.ptr

export %inline
usec : STimeval -> PrimIO SusecondsT
usec s = get_timeval_tv_usec s.ptr

export %inline
setsec : STimeval -> TimeT -> PrimIO ()
setsec s v = set_timeval_tv_sec s.ptr v

export %inline
setusec : STimeval -> SusecondsT -> PrimIO ()
setusec s v = set_timeval_tv_usec s.ptr v

||| Pure alternative to the `STimeval` struct.
public export
record Timeval where
  constructor TV
  sec  : TimeT
  usec : SusecondsT

%runElab derive "Timeval" [Show,Eq]

export %inline
stimeval : Timeval -> PrimIO STimeval
stimeval (TV s u) = primMap STV $ prim__timeval s u

export
timeval : STimeval -> PrimIO Timeval
timeval stv w =
  let MkIORes sec  w := Timer.sec stv w
      MkIORes usec w := Timer.usec stv w
   in MkIORes (TV sec usec) w

--------------------------------------------------------------------------------
-- Itimerval
--------------------------------------------------------------------------------

%foreign "C:get_itimerval_it_interval, posix-idris"
get_itimerval_it_interval: AnyPtr -> PrimIO AnyPtr

%foreign "C:get_itimerval_it_value, posix-idris"
get_itimerval_it_value: AnyPtr -> PrimIO AnyPtr

%foreign "C:set_itimerval_it_interval, posix-idris"
set_itimerval_it_interval: AnyPtr -> AnyPtr -> PrimIO ()

%foreign "C:set_itimerval_it_value, posix-idris"
set_itimerval_it_value: AnyPtr -> AnyPtr -> PrimIO ()

%foreign "C:li_itimerval, posix-idris"
prim__itimerval : TimeT -> SusecondsT -> TimeT -> SusecondsT -> PrimIO AnyPtr

export
record Itimerval where
  constructor ITV
  ptr : AnyPtr

export %inline
Struct Itimerval where
  wrap   = ITV
  unwrap = ptr

export %inline
SizeOf Itimerval where
  sizeof_ = itimerval_size

export %inline
interval : Itimerval -> PrimIO STimeval
interval s = primMap STV $ get_itimerval_it_interval s.ptr

export %inline
value : Itimerval -> PrimIO STimeval
value s = primMap STV $ get_itimerval_it_value s.ptr

export %inline
setinterval : Itimerval -> STimeval -> PrimIO ()
setinterval s v = set_itimerval_it_interval s.ptr v.ptr

export %inline
setvalue : Itimerval -> STimeval -> PrimIO ()
setvalue s v = set_itimerval_it_value s.ptr v.ptr

||| Pure alternative to the `Itimerval` struct.
public export
record Timerval where
  constructor TRV
  interval : Timeval
  value    : Timeval

%runElab derive "Timerval" [Show,Eq]

||| Creates and sets the fields of a `Itimerval` pointer.
|||
||| The allocated memory must be freed via `freeStruct`.
export %inline
itimerval : Timerval -> PrimIO Itimerval
itimerval (TRV (TV si ui) (TV sv uv)) = do
  primMap ITV $ prim__itimerval si ui sv uv

export
timerval : Itimerval -> PrimIO Timerval
timerval itv w =
  let MkIORes siv  w := interval itv w
      MkIORes iv   w := timeval siv w
      MkIORes sval w := value itv w
      MkIORes val  w := timeval sval w
   in MkIORes (TRV iv val) w

--------------------------------------------------------------------------------
-- Itimerspec
--------------------------------------------------------------------------------

export %foreign "C:get_itimerspec_it_interval, posix-idris"
get_itimerspec_it_interval: AnyPtr -> PrimIO AnyPtr

export %foreign "C:get_itimerspec_it_value, posix-idris"
get_itimerspec_it_value: AnyPtr -> PrimIO AnyPtr

export %foreign "C:set_itimerspec_it_interval, posix-idris"
set_itimerspec_it_interval: AnyPtr -> AnyPtr -> PrimIO ()

export %foreign "C:set_itimerspec_it_value, posix-idris"
set_itimerspec_it_value: AnyPtr -> AnyPtr -> PrimIO ()

%foreign "C:li_itimerspec, posix-idris"
prim__itimerspec : TimeT -> NsecT -> TimeT -> NsecT -> PrimIO AnyPtr

||| Note: Also this is POSIX compliant, it is not available on
||| MacOS (Darwin). Idris programs making use of this might fail on
||| Darwin during code generation.
export
record Itimerspec where
  constructor ITS
  ptr : AnyPtr

export %inline
Struct Itimerspec where
  wrap   = ITS
  unwrap = ptr

export %inline
SizeOf Itimerspec where
  sizeof_ = itimerspec_size

namespace Itimerspec
  export %inline
  interval : Itimerspec -> PrimIO STimespec
  interval s = primMap wrap $ get_itimerspec_it_interval s.ptr

  export %inline
  value : Itimerspec -> PrimIO STimespec
  value s = primMap wrap $ get_itimerspec_it_value s.ptr


  export %inline
  setinterval : Itimerspec -> STimespec -> PrimIO ()
  setinterval s v = set_itimerspec_it_interval s.ptr (unwrap v)

  export %inline
  setvalue : Itimerspec -> STimespec -> PrimIO ()
  setvalue s v = set_itimerspec_it_value s.ptr (unwrap v)

||| Creates and sets the fields of a `Itimerspec` pointer.
|||
||| The allocated memory must be freed via `freeStruct`.
export %inline
itimerspec :
     (secInterval  : TimeT)
  -> (usecInterval : NsecT)
  -> (secValue     : TimeT)
  -> (usecValue    : NsecT)
  -> PrimIO Itimerspec
itimerspec si ni sv nv = do
  primMap ITS $ prim__itimerspec si ni sv nv

||| Pure alternative to the `Itimerspec` struct.
public export
record Timerspec where
  constructor TS
  interval : Clock Monotonic
  value    : Clock Monotonic

%runElab derive "Timerspec" [Show,Eq]

export
timerspec : Itimerspec -> PrimIO Timerspec
timerspec its w =
  let MkIORes siv  w := Itimerspec.interval its w
      MkIORes iv   w := toClock siv w
      MkIORes sval w := Itimerspec.value its w
      MkIORes val  w := toClock sval w
   in MkIORes (TS iv val) w

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_setitimer, posix-idris"
prim__setitimer : Bits8 -> AnyPtr -> AnyPtr -> PrimIO CInt

%foreign "C:li_setitimer1, posix-idris"
prim__setitimer1 : Bits8 -> TimeT -> SusecondsT -> TimeT -> SusecondsT -> PrimIO CInt

%foreign "C:getitimer, posix-idris"
prim__getitimer : Bits8 -> AnyPtr -> PrimIO ()

%foreign "C:li_clock_gettime, posix-idris"
prim__clock_gettime : Bits8 -> AnyPtr -> PrimIO CInt

%foreign "C:li_clock_getres, posix-idris"
prim__clock_getres : Bits8 -> AnyPtr -> PrimIO CInt

%foreign "C:li_nanosleep, posix-idris"
prim__nanosleep : AnyPtr -> AnyPtr -> PrimIO CInt

%foreign "C:li_nanosleep1, posix-idris"
prim__nanosleep1 : TimeT -> NsecT -> PrimIO CInt

%foreign "C:li_clock_nanosleep, posix-idris"
prim__clock_nanosleep : Bits8 -> AnyPtr -> AnyPtr -> PrimIO Bits32

%foreign "C:li_clock_nanosleep_abs, posix-idris"
prim__clock_nanosleep_abs : Bits8 -> AnyPtr -> PrimIO Bits32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Returns an approximation of processor time used by the program.
|||
||| Type `ClockT` measures time with a granularity of
||| `CLOCKS_PER_SEC`.
export %foreign "C:clock, posix-idris"
clock : PrimIO ClockT

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
setitimer : Which -> (new,old : Itimerval) -> PrimIO (Either Errno ())
setitimer w (ITV n) (ITV o) = toUnit $ prim__setitimer (whichCode w) n o

||| Writes the currently set timer for `Which` into `old.
export %inline
getitimer : Which -> (old : Itimerval) -> PrimIO ()
getitimer w (ITV o) = prim__getitimer (whichCode w) o

||| A very basic version of `setitimer` that raises `SIGALRM`
||| after the given number of seconds.
|||
||| The returned value is the remaining number of seconds on any
||| previously set timer. The timer can be disabled by setting
||| this to zero.
export %foreign "C:alarm, posix-idris"
alarm : UInt -> PrimIO UInt

||| Writes the current time for the given clock into the
||| `STimespec` pointer.
export %inline
clockGetTime : ClockId -> STimespec -> PrimIO (Either Errno ())
clockGetTime c t = toUnit $ prim__clock_gettime (clockCode c) (unwrap t)

||| Writes the resolution for the given clock into the
||| `STimespec` pointer.
export %inline
clockGetRes : ClockId -> STimespec -> PrimIO (Either Errno ())
clockGetRes c t = toUnit $ prim__clock_getres (clockCode c) (unwrap t)

||| High resolution sleeping for the duration given in `dur`.
|||
||| In case this is interrupted by a signal, it returns `Left EINTR`
||| and writes the remaining duration into `rem`.
export %inline
nanosleep : (dur,rem : STimespec) -> PrimIO (Either Errno ())
nanosleep d r = toUnit $ prim__nanosleep (unwrap d) (unwrap r)

||| Like `nanosleep` but allows us to specify the system clock to use.
export %inline
clockNanosleep : ClockId -> (dur,rem : STimespec) -> PrimIO (Either Errno ())
clockNanosleep c d r =
  posToUnit $ prim__clock_nanosleep (clockCode c) (unwrap d) (unwrap r)

||| Like `clockNanosleep` but uses an absolute time value instead of a duration.
|||
||| This is useful to get exact wakeup times even in case of lots of signal
||| interrupts.
export %inline
clockNanosleepAbs : ClockId -> (time : STimespec) -> PrimIO (Either Errno ())
clockNanosleepAbs c d =
  posToUnit $ prim__clock_nanosleep_abs (clockCode c) (unwrap d)

--------------------------------------------------------------------------------
-- Convenience API
--------------------------------------------------------------------------------

public export
ClockTpe : ClockId -> ClockType
ClockTpe CLOCK_REALTIME           = UTC
ClockTpe CLOCK_MONOTONIC          = Monotonic
ClockTpe CLOCK_PROCESS_CPUTIME_ID = Process
ClockTpe CLOCK_THREAD_CPUTIME_ID  = Thread

public export
IClock : ClockId -> Type
IClock = Clock . ClockTpe

||| Like `setitimer` but does not store the old timer in a pointer.
|||
||| TODO: We could avoid the possibility for failure by checking that
|||       the `SusecondsT` values are within bounds: [0 ... 999_999]
export %inline
setTimer : Which -> Timerval -> PrimIO (Either Errno ())
setTimer w (TRV (TV si ui) (TV sv uv)) =
  toUnit $ prim__setitimer1 (whichCode w) si ui sv uv

||| Returns the currently set timer for `Which`.
export
getTimer : Which -> PrimIO Timerval
getTimer wh =
  withStruct Itimerval $ \str,w =>
  let MkIORes _ w := getitimer wh str w
   in timerval str w

||| Returns the current time for the given clock.
export
getTime : (c : ClockId) -> PrimIO (Either Errno $ IClock c)
getTime c =
  withStruct STimespec $ \str,w =>
    let MkIORes (Right ()) w := clockGetTime c str w
          | MkIORes (Left x) w => MkIORes (Left x) w
     in primMap Right (toClock str) w

||| Returns the resolution for the given clock.
export
getResolution : (c : ClockId) -> PrimIO (Either Errno $ IClock c)
getResolution c =
  withStruct STimespec $ \str,w =>
    let MkIORes (Right ()) w := clockGetRes c str w
          | MkIORes (Left x) w => MkIORes (Left x) w
     in primMap Right (toClock str) w

||| Like `nanosleep` but without the capability of keeping track of the
||| remaining duration in case of a signal interrupt.
export %inline
nanosleep' : (dur : Clock Monotonic) -> PrimIO (Either Errno ())
nanosleep' cl =
  toUnit $ prim__nanosleep1 (cast $ seconds cl) (cast $ nanoseconds cl)
