module System.Linux.Pthreads

import Data.C.Ptr
import System.Posix.Signal
import public System.Posix.Pthreads

%default total

%foreign "C:li_pthread_sigqueue, posix-idris"
prim__pthread_sigqueue : AnyPtr -> Bits32 -> CInt -> PrimIO Bits32

||| Sends a realtime signal plus data word to a thread.
|||
||| Note that `sig` must be in the range [SIGRTMIN, SIGRTMAX].
export %inline
pthreadSigqueue : PthreadT -> Signal -> (word : CInt) -> IO (Either Errno ())
pthreadSigqueue p s word =
  posToUnit $ prim__pthread_sigqueue (unwrapPthreadT p) s.sig word
