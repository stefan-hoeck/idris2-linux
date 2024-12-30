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
|||
||| Notes:
||| * A `signalfd` should be closed using `close` just like other file
|||   descriptors.
||| * In general, use `readTimerfd` instead of the `read` functions
|||   from `System.Posix.File` to read from a `timerfd`.
export %inline
timerfd : ErrIO io => ClockId -> TimerfdFlags -> io Timerfd
timerfd c = eprim . P.timerfd c

||| Sets the time of a `timerfd`.
|||
||| The currently set time will be stored in `old`.
||| Use the `TFD_TIMER_ABSTIME` flag if the time should be interpreted as
||| an absolute wall clock time.
export %inline
setitime : ErrIO io => Timerfd -> Bits32 -> (new,old : Itimerspec) -> io ()
setitime t f new = eprim . P.setitime t f new

||| Reads the currently set `itimerspec` of a `timerfd` and uses the given
||| pointer to place the data.
export %inline
getitime : HasIO io => Timerfd -> (old : Itimerspec) -> io ()
getitime t = primIO . P.getitime t

||| Reads data from a `timerfd`.
|||
||| This will block until the next time the timer expires unless `TFD_NONBLOCK`
||| was set when creating the timer.
|||
||| The value returned is the number of times the timer expired since
||| the last read.
export %inline
readTimerfd : ErrIO io => Timerfd -> io Bits64
readTimerfd = eprim . P.readTimerfd

--------------------------------------------------------------------------------
-- Convenience API
--------------------------------------------------------------------------------

||| Like `setitime` but without storing the currently set `itimerspec`.
export %inline
setTime : ErrIO io => Timerfd -> Bits32 -> Timerspec -> io ()
setTime t f = eprim . P.setTime t f

||| Convenience alias for `getitime`.
export %inline
getTime : ErrIO io => Timerfd -> io Timerspec
getTime = eprim . P.getTime
