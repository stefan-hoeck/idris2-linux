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
signalfd_ : Has Errno es => EIO1 f => (set : SigsetT) -> SignalfdFlags -> f es Signalfd
signalfd_ set fs = elift1 (P.signalfd_ set fs)

--------------------------------------------------------------------------------
-- Convenience API
--------------------------------------------------------------------------------

||| Convenience alias for `signalfd_`.
export %inline
signalfd : Has Errno es => EIO1 f => List Signal -> SignalfdFlags -> f es Signalfd
signalfd ss fs = elift1 (P.signalfd ss fs)

||| Reads data from a `signalfd` into a pre-allocated array.
|||
||| Note: This will overwrite the data stored in `arr` and the
|||       result is a wrapper around the same pointer.
export
readSignalfd : Has Errno es => EIO1 f => Signalfd -> Nat -> f es (List Siginfo)
readSignalfd fd n = elift1 (P.readSignalfd fd n)
