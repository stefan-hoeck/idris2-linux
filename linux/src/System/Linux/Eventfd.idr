module System.Linux.Eventfd

import System.Linux.Eventfd.Prim as P

import public Data.C.Ptr
import public System.Linux.Eventfd.Eventfd
import public System.Linux.Eventfd.Flags
import public System.Posix.File

%default total

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
eventfd : Has Errno es => EIO1 f => (init : Bits64) -> EventfdFlags -> f es Eventfd
eventfd init fs = elift1 (P.eventfd init fs)

||| Writes a value to the given event file descriptor.
export %inline
writeEventfd : Has Errno es => EIO1 f => Eventfd -> Bits64 -> f es ()
writeEventfd fd v = elift1 (P.writeEventfd fd v)

||| Reads the current value from an event file descriptor.
|||
||| If the current value is 0, this will block until a non-zero value
||| is ready. If opened with the `EFD_NONBLOCK` flag, this fails with `EAGAIN`
||| if no value is ready. If opened with the `EFD_SEMAPHORE` flag, this will
||| return 1 if a value is ready and reduce the value by 1.
export %inline
readEventfd : Has Errno es => EIO1 f => Eventfd -> f es Bits64
readEventfd fd = elift1 (P.readEventfd fd)
