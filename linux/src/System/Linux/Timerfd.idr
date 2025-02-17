module System.Linux.Timerfd

import System.Linux.Timerfd.Prim as P


import public Data.C.Ptr
import public System.Linux.Timerfd.Flags
import public System.Linux.Timerfd.Timerfd
import public System.Posix.File
import public System.Posix.Timer

%default total

||| Opens a new `timerfd` file descriptor for observing the given clock.
|||
||| Notes:
||| * A `timerfd` should be closed using `close` just like other file
|||   descriptors.
||| * In general, use `readTimerfd` instead of the `read` functions
|||   from `System.Posix.File` to read from a `timerfd`.
export %inline
timerfd : Has Errno es => EIO1 f => ClockId -> TimerfdFlags -> f es Timerfd
timerfd c fs = elift1 (P.timerfd c fs)

||| Sets the time of a `timerfd`.
|||
||| The currently set time will be stored in `old`.
||| Use the `TFD_TIMER_ABSTIME` flag if the time should be interpreted as
||| an absolute wall clock time.
export %inline
setitime : Has Errno es => EIO1 f => Timerfd -> Bits32 -> (new,old : IOTimerspec) -> f es ()
setitime t f new old = elift1 (P.setitime t f new old)

||| Reads the currently set `itimerspec` of a `timerfd` and uses the given
||| pointer to place the data.
export %inline
getitime : HasIO io => Timerfd -> (old : IOTimerspec) -> io ()
getitime t = primIO . P.getitime t

||| Reads data from a `timerfd`.
|||
||| This will block until the next time the timer expires unless `TFD_NONBLOCK`
||| was set when creating the timer.
|||
||| The value returned is the number of times the timer expired since
||| the last read.
export %inline
readTimerfd : Has Errno es => EIO1 f => Timerfd -> f es Bits64
readTimerfd fd = elift1 (P.readTimerfd fd)

--------------------------------------------------------------------------------
-- Convenience API
--------------------------------------------------------------------------------

||| Like `setitime` but without storing the currently set `itimerspec`.
export %inline
setTime : Has Errno es => EIO1 f => Timerfd -> Bits32 -> Timerspec -> f es ()
setTime t f n = elift1 (P.setTime t f n)

||| Convenience alias for `getitime`.
export %inline
getTime : Has Errno es => EIO1 f => Timerfd -> f es Timerspec
getTime fd = elift1 (P.getTime fd)
