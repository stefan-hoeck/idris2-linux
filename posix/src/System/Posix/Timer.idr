module System.Posix.Timer

import Data.C.Ptr

import System.Posix.Timer.Prim as P

import public Data.C.Integer
import public System.Posix.Errno
import public System.Posix.Timer.Types
import public System.Posix.Time

%default total

||| Returns an approximation of processor time used by the program.
|||
||| Type `ClockT` measures time with a granularity of
||| `CLOCKS_PER_SEC`.
export %inline
clock : HasIO io => io ClockT
clock = primIO P.clock

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
setTimer : Has Errno es => EIO1 f => Which -> Timerval -> f es ()
setTimer w t = elift1 (P.setTimer w t)

||| Returns the currently set timer for `Which`.
export %inline
getTimer : Has Errno es => EIO1 f => Which -> f es Timerval
getTimer w = elift1 (P.getTimer w)

||| A very basic version of `setitimer` that raises `SIGALRM`
||| after the given number of seconds.
|||
||| The returned value is the remaining number of seconds on any
||| previously set timer. The timer can be disabled by setting
||| this to zero.
export %inline
alarm : HasIO io => UInt -> io UInt
alarm u = primIO (P.alarm u)

||| Returns the current time for the given clock.
export %inline
getTime : Has Errno es => EIO1 f => (c : ClockId) -> f es (IClock c)
getTime c = elift1 (P.getTime c)

||| Returns the resolution for the given clock.
export %inline
getResolution : Has Errno es => EIO1 f => (c : ClockId) -> f es (IClock c)
getResolution c = elift1 (P.getResolution c)

||| Like `nanosleep` but without the capability of keeping track of the
||| remaining duration in case of a signal interrupt.
export %inline
nanosleep : Has Errno es => EIO1 f => (dur : Clock Monotonic) -> f es ()
nanosleep cl = elift1 (P.nanosleep cl)
