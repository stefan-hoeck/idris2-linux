module System.Linux.Timerfd

import public Data.C.Ptr
import public System.Linux.Timerfd.Flags
import public System.Posix.File
import public System.Posix.Timer

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_timerfd_create, linux-idris"
prim__timerfd_create : Bits8 -> Bits32 -> PrimIO CInt

%foreign "C:li_timerfd_settime, linux-idris"
prim__timerfd_settime : Bits32 -> Bits32 -> AnyPtr -> AnyPtr -> PrimIO CInt

%foreign "C:li_timerfd_settime1, linux-idris"
prim__timerfd_settime1 : Bits32 -> Bits32 -> AnyPtr -> PrimIO CInt

%foreign "C:li_timerfd_gettime, linux-idris"
prim__timerfd_gettime : Bits32 -> AnyPtr -> PrimIO CInt

%foreign "C:li_timerfd_read, linux-idris"
prim__timerfd_read : Bits32 -> PrimIO Int64

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| A file descriptor for signal handling.
|||
||| This can be used for synchronous signal handling using
||| (blocking) `readSignalfd` directly, or for asynchronous signal handling
||| using `epoll`.
export
record Timerfd where
  constructor TFD
  fd : Bits32

export %inline
Cast Timerfd Fd where cast = MkFd . fd

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
timerfd c (F f) = toVal (TFD . cast) $ prim__timerfd_create (clockCode c) f

||| Sets the time of a `timerfd`.
|||
||| The currently set time will be stored in `old`.
||| Use the `TFD_TIMER_ABSTIME` flag if the time should be interpreted as
||| an absolute wall clock time.
export %inline
settime : ErrIO io => Timerfd -> Bits32 -> (new,old : Itimerspec) -> io ()
settime t f new old =
  toUnit $ prim__timerfd_settime t.fd f (unwrap new) (unwrap old)

||| Like `settime` but without storing the currently set `itimerspec`.
export %inline
settime' : ErrIO io => Timerfd -> Bits32 -> (new : Itimerspec) -> io ()
settime' t f new = toUnit $ prim__timerfd_settime1 t.fd f (unwrap new)

||| Reads the currently set `itimerspec` of a `timerfd` and uses the given
||| pointer to place the data.
export %inline
gettime : ErrIO io => Timerfd -> (old : Itimerspec) -> io ()
gettime t old = toUnit $ prim__timerfd_gettime t.fd (unwrap old)

||| Reads data from a `timerfd`.
|||
||| This will block until the next time the timer expires unless `TFD_NONBLOCK`
||| was set when creating the timer.
|||
||| The value returned is the number of times the timer expired since
||| the last read.
export %inline
readTimerfd : ErrIO io => Timerfd -> io Bits64
readTimerfd t = do
  r <- primIO $ prim__timerfd_read t.fd
  if r < 0 then error (fromNeg r) else pure (cast r)
