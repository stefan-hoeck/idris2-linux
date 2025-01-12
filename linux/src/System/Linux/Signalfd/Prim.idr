module System.Linux.Signalfd.Prim

import System.Posix.File.Prim
import System.Posix.Signal.Prim

import public Data.C.Ptr
import public System.Linux.Signalfd.Flags
import public System.Linux.Signalfd.Struct

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_signalfd, linux-idris"
prim__signalfd : AnyPtr -> Bits32 -> PrimIO CInt

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
signalfd_ : (set : SigsetT) -> SignalfdFlags -> EPrim Signalfd
signalfd_ set (F f) = toVal cast $ prim__signalfd (unwrap set) f

--------------------------------------------------------------------------------
-- Convenience API
--------------------------------------------------------------------------------

||| Convenience alias for `signalfd_`.
export %inline
signalfd : List Signal -> SignalfdFlags -> EPrim Signalfd
signalfd ss fs = withSignals ss $ \set => signalfd_ set fs

||| Reads at most `n` values of type `Siginfo` from a `Signalfd`.
export %inline
readSignalfd : Signalfd -> Nat -> EPrim (List Siginfo)
readSignalfd fd n = read fd _ (cast n * sizeof SiginfoT)
