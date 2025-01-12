module System.Linux.Signalfd

import System.Linux.Signalfd.Prim as P

import public Data.C.Ptr
import public System.Linux.Signalfd.Flags
import public System.Linux.Signalfd.Struct
import public System.Posix.File
import public System.Posix.Signal

%default total

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Opens a new `signalfd` file descriptor for observing the
||| signals specified in the given `SigsetT`.
|||
|||
||| Notes:
||| * Usually, the signals in `set` should first be blocked via `sigprocmask`.
||| * A `signalfd` should be closed using `close` just like other file
|||   descriptors.
||| * In general, use `readSignalfd` instead of the `read` functions
|||   from `System.Posix.File` to read from a `signalfd`.
export %inline
signalfd_ : ErrIO io => (set : SigsetT) -> SignalfdFlags -> io Signalfd
signalfd_ set = eprim . P.signalfd_ set

--------------------------------------------------------------------------------
-- Convenience API
--------------------------------------------------------------------------------

||| Convenience alias for `signalfd_`.
export %inline
signalfd : ErrIO io => List Signal -> SignalfdFlags -> io Signalfd
signalfd ss = eprim . P.signalfd ss

||| Reads data from a `signalfd` into a pre-allocated array.
|||
||| Note: This will overwrite the data stored in `arr` and the
|||       result is a wrapper around the same pointer.
export
readSignalfd : ErrIO io => Signalfd -> Nat -> io (List Siginfo)
readSignalfd fd = eprim . P.readSignalfd fd
