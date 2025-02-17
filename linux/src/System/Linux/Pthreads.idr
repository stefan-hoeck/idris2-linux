module System.Linux.Pthreads

import System.Linux.Pthreads.Prim as P

import Data.C.Ptr
import System.Posix.Signal
import public System.Posix.Pthreads

%default total

||| Sends a realtime signal plus data word to a thread.
|||
||| Note that `sig` must be in the range [SIGRTMIN, SIGRTMAX].
export %inline
pthreadSigqueue : Has Errno es => EIO1 f => PthreadT -> Signal -> (word : CInt) -> f es ()
pthreadSigqueue p s word = elift1 (P.pthreadSigqueue p s word)
