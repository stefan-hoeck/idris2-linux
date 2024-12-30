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
pthreadSigqueue : ErrIO io => PthreadT -> Signal -> (word : CInt) -> io ()
pthreadSigqueue p s = eprim . P.pthreadSigqueue p s
