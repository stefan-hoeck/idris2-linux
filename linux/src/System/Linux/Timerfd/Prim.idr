module System.Linux.Timerfd.Prim

import public Data.C.Ptr
import public System.Linux.Timerfd.Flags
import public System.Linux.Timerfd.Timerfd
import public System.Posix.File.Prim
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
prim__timerfd_settime1 : Bits32 -> Bits32 -> TimeT -> NsecT -> TimeT -> NsecT -> PrimIO CInt

%foreign "C:li_timerfd_gettime, linux-idris"
prim__timerfd_gettime : Bits32 -> AnyPtr -> PrimIO ()

%foreign "C:li_timerfd_read, linux-idris"
prim__timerfd_read : Bits32 -> PrimIO Int64

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Opens a new `timerfd` file descriptor for observing the given clock.
|||
|||
||| Notes:
||| * A `signalfd` should be closed using `close` just like other file
|||   descriptors.
||| * In general, use `readTimerfd` instead of the `read` functions
|||   from `System.Posix.File` to read from a `timerfd`.
export %inline
timerfd : ClockId -> TimerfdFlags -> EPrim Timerfd
timerfd c (F f) = toVal cast $ prim__timerfd_create (clockCode c) f

||| Sets the time of a `timerfd`.
|||
||| The currently set time will be stored in `old`.
||| Use the `TFD_TIMER_ABSTIME` flag if the time should be interpreted as
||| an absolute wall clock time.
export %inline
setitime : Timerfd -> Bits32 -> (new,old : IOTimerspec) -> EPrim ()
setitime t f new old =
  toUnit $ prim__timerfd_settime (fileDesc t) f (unwrap new) (unwrap old)

||| Reads the currently set `itimerspec` of a `timerfd` and uses the given
||| pointer to place the data.
export %inline
getitime : Timerfd -> (old : IOTimerspec) -> PrimIO ()
getitime t old = prim__timerfd_gettime (fileDesc t) (unwrap old)

||| Reads data from a `timerfd`.
|||
||| This will block until the next time the timer expires unless `TFD_NONBLOCK`
||| was set when creating the timer.
|||
||| The value returned is the number of times the timer expired since
||| the last read.
export %inline
readTimerfd : Timerfd -> EPrim Bits64
readTimerfd fd t =
  let r # t := ffi (prim__timerfd_read (fileDesc fd)) t
   in if r < 0 then E (fromNeg r) t else R (cast r) t

--------------------------------------------------------------------------------
-- Convenience API
--------------------------------------------------------------------------------

||| Like `setitime` but without storing the currently set `itimerspec`.
export %inline
setTime : Timerfd -> Bits32 -> Timerspec -> EPrim ()
setTime t f (TS i v) =
  toUnit $ prim__timerfd_settime1 (fileDesc t) f i.secs i.nsecs v.secs v.nsecs

||| Convenience alias for `getitime`.
export %inline
getTime : Timerfd -> EPrim Timerspec
getTime fd =
  withStruct IOTimerspec $ \str,t =>
    let _  # t := toF1 (getitime fd str) t
        ts # t := timerspec str t
     in R ts t
