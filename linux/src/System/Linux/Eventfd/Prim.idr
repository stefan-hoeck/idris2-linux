module System.Linux.Eventfd.Prim

import Data.C.Ptr
import public System.Linux.Eventfd.Eventfd
import public System.Linux.Eventfd.Flags
import public System.Posix.File.Prim

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_eventfd, linux-idris"
prim__eventfd : Bits64 -> Bits32 -> PrimIO CInt

%foreign "C:li_eventfd_write, linux-idris"
prim__eventfd_write : Bits32 -> Bits64 -> PrimIO CInt

%foreign "C:li_eventfd_read, linux-idris"
prim__eventfd_read : Bits32 -> PrimIO CInt

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Opens a new `eventfd` file descriptor writing the given value
||| to it.
|||
||| Notes:
||| * An `eventfd` should be closed using `close` just like other file
|||   descriptors.
||| * In general, use `readEventfd` instead of the `read` functions
|||   from `System.Posix.File` to read from an `eventfd`.
||| * Likewise, use `writeEventfd` instead of `System.Posix.File.write`
export %inline
eventfd : (init : Bits64) -> EventfdFlags -> EPrim Eventfd
eventfd init (F f) = toVal cast $ prim__eventfd init f

||| Writes a value to the given event file descriptor.
export %inline
writeEventfd : Eventfd -> Bits64 -> EPrim ()
writeEventfd t val = toUnit $ prim__eventfd_write (fileDesc t) val

||| Reads the current value from an event file descriptor.
|||
||| If the current value is 0, this will block until a non-zero value
||| is ready. If opened with the `EFD_NONBLOCK` flag, this fails with `EAGAIN`
||| if no value is ready. If opened with the `EFD_SEMAPHORE` flag, this will
||| return 1 if a value is ready and reduce the value by 1.
export %inline
readEventfd : Eventfd -> EPrim Bits64
readEventfd t = toVal cast $ prim__eventfd_read (fileDesc t)
