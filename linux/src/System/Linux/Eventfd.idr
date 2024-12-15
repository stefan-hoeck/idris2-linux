module System.Linux.Eventfd

import public Data.C.Ptr
import public System.Linux.Eventfd.Flags
import public System.Posix.File

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

||| A file descriptor for basic file events.
|||
||| This can be used as an event wait/notify mechanism similar to
||| a `Condition` variable.
export
record Eventfd where
  constructor EFD
  fd : Bits32

export %inline
Cast Eventfd Fd where cast = MkFd . fd

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
eventfd : ErrIO io => (init : Bits64) -> EventfdFlags -> io Eventfd
eventfd init (F f) = toVal (EFD . cast) $ prim__eventfd init f

||| Writes a value to the given event file descriptor.
export %inline
writeEventfd : ErrIO io => Eventfd -> Bits64 -> io ()
writeEventfd t val = toUnit $ prim__eventfd_write t.fd val

||| Reads the current value from an event file descriptor.
|||
||| If the current value is 0, this will block until a non-zero value
||| is ready. If opened with the `EFD_NONBLOCK` flag, this fails with `EAGAIN`
||| if no value is ready. If opened with the `EFD_SEMAPHORE` flag, this will
||| return 1 if a value is ready and reduce the value by 1.
export %inline
readEventfd : ErrIO io => Eventfd -> io Bits64
readEventfd t = toVal cast $ prim__eventfd_read t.fd
