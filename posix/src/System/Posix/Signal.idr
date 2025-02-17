module System.Posix.Signal

import Data.C.Ptr

import System.Posix.Signal.Prim as P

import public Data.C.Integer
import public System.Posix.Errno
import public System.Posix.Signal.Struct
import public System.Posix.Signal.Types

%default total

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Sends a signal to a running process or a group of processes.
export %inline
kill : Has Errno es => EIO1 f => PidT -> Signal -> f es ()
kill p s = elift1 (P.kill p s)

||| Sends a signal to the calling thread.
export %inline
raise : HasIO io => Signal -> io ()
raise s = primIO (P.raise s)

||| Sends a realtime signal plus data word to a running process.
|||
||| Note that `sig` must be in the range [SIGRTMIN, SIGRTMAX].
export %inline
sigqueue : Has Errno es => EIO1 f => PidT -> Signal -> (word : CInt) -> f es ()
sigqueue p s word = elift1 (P.sigqueue p s word)

||| Adjust the process signal mask according to the given `How`
||| and signal set.
export %inline
sigprocmask : Has Errno es => EIO1 f => How -> List Signal -> f es ()
sigprocmask h ss = elift1 (P.sigprocmask h ss)

||| Terminates the application by raising `SIGABRT` and dumps core.
|||
||| While `SIGABRT` can be handled with a signal handler, `abort` is
||| still guaranteed successfully terminate the process.
export %inline
abort : HasIO io => io ()
abort = primIO P.abort

||| Suspends the current thread until a non-blocked signal is encountered.
export %inline
pause : Has Errno es => EIO1 f => f es ()
pause = elift1 P.pause

||| Returns the current signal mask of the process.
export %inline
siggetprocmask : HasIO io => io (List Signal)
siggetprocmask = primIO P.siggetprocmask

||| Returns the set of currently pending signals.
export %inline
sigpending : HasIO io => io (List Signal)
sigpending = primIO P.sigpending

||| Atomically blocks the signals in `set`, then
||| pauses the thread (see `pause`) and restores the signal set
||| afterwards.
export %inline
sigsuspend : Has Errno es => EIO1 f => List Signal -> f es ()
sigsuspend ss = elift1 (P.sigsuspend ss)

||| Synchronously awaits one of the signals in `set`.
|||
||| This is like `sigwaitinfo` but with a simpler API.
export %inline
sigwait : Has Errno es => EIO1 f => List Signal -> f es Signal
sigwait ss = elift1 (P.sigwait ss)

||| Synchronously awaits one of the signals in `set`.
|||
||| Note: Usually, the signals in `set` should first be blocked via
|||       `sigprocmask`.
export
sigwaitinfo : Has Errno es => EIO1 f => List Signal -> f es Siginfo
sigwaitinfo ss = elift1 (P.sigwaitinfo ss)
