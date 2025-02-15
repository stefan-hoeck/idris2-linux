module System.Posix.Timer.Prim

import Data.C.Ptr

import public Data.C.Integer
import public System.Posix.Errno
import public System.Posix.Timer.Types
import public System.Posix.Time

%default total

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
setitimer : Which -> (new,old : IOTimerval) -> EPrim ()
setitimer w n o = toUnit $ prim__setitimer (whichCode w) (unwrap n) (unwrap o)

||| Writes the currently set timer for `Which` into `old.
export %inline
getitimer : Which -> (old : IOTimerval) -> PrimIO ()
getitimer w o = prim__getitimer (whichCode w) (unwrap o)

||| A very basic version of `setitimer` that raises `SIGALRM`
||| after the given number of seconds.
|||
||| The returned value is the remaining number of seconds on any
||| previously set timer. The timer can be disabled by setting
||| this to zero.
export %foreign "C:alarm, posix-idris"
alarm : UInt -> PrimIO UInt

||| Writes the current time for the given clock into the
||| `IOTimespec` pointer.
export %inline
clockGetTime : ClockId -> IOTimespec -> EPrim ()
clockGetTime c t = toUnit $ prim__clock_gettime (clockCode c) (unwrap t)

||| Writes the resolution for the given clock into the
||| `IOTimespec` pointer.
export %inline
clockGetRes : ClockId -> IOTimespec -> EPrim ()
clockGetRes c t = toUnit $ prim__clock_getres (clockCode c) (unwrap t)

||| High resolution sleeping for the duration given in `dur`.
|||
||| In case this is interrupted by a signal, it returns `Left EINTR`
||| and writes the remaining duration into `rem`.
export %inline
nanosleep_ : (dur,rem : IOTimespec) -> EPrim ()
nanosleep_ d r = toUnit $ prim__nanosleep (unwrap d) (unwrap r)

||| Like `nanosleep` but allows us to specify the system clock to use.
export %inline
clockNanosleep : ClockId -> (dur,rem : IOTimespec) -> EPrim ()
clockNanosleep c d r =
  posToUnit $ prim__clock_nanosleep (clockCode c) (unwrap d) (unwrap r)

||| Like `clockNanosleep` but uses an absolute time value instead of a duration.
|||
||| This is useful to get exact wakeup times even in case of lots of signal
||| interrupts.
export %inline
clockNanosleepAbs : ClockId -> (time : IOTimespec) -> EPrim ()
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
export %inline
setTimer : Which -> Timerval -> EPrim ()
setTimer w (TRV (TV si ui) (TV sv uv)) =
  toUnit $ prim__setitimer1 (whichCode w) si ui sv uv

||| Returns the currently set timer for `Which`.
export
getTimer : Which -> EPrim Timerval
getTimer wh =
  withStruct IOTimerval $ \str,t =>
    let _ # t := toF1 (getitimer wh str) t
        r # t := timerval str t
     in R r t

||| Returns the current time for the given clock.
export
getTime : (c : ClockId) -> EPrim (IClock c)
getTime c =
  withStruct IOTimespec $ \str,t =>
    let R _ t := clockGetTime c str t | E x t => E x t
        c # t := toClock str t
     in R c t

||| Returns the resolution for the given clock.
export
getResolution : (c : ClockId) -> EPrim (IClock c)
getResolution c =
  withStruct IOTimespec $ \str,t =>
    let R _ t := clockGetRes c str t | E x t => E x t
        c # t := toClock str t
     in R c t

||| Like `nanosleep` but without the capability of keeping track of the
||| remaining duration in case of a signal interrupt.
export %inline
nanosleep : (dur : Clock Monotonic) -> EPrim ()
nanosleep cl = toUnit $ prim__nanosleep1 cl.secs cl.nsecs
