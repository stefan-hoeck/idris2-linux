module System.Linux.Pthreads.Prim

import Data.C.Ptr
import System.Posix.Signal.Prim
import System.Posix.Pthreads.Prim

%default total

%foreign "C:li_pthread_sigqueue, posix-idris"
prim__pthread_sigqueue : AnyPtr -> Bits32 -> CInt -> PrimIO Bits32

||| Sends a realtime signal plus data word to a thread.
|||
||| Note that `sig` must be in the range [SIGRTMIN, SIGRTMAX].
export %inline
pthreadSigqueue : PthreadT -> Signal -> (word : CInt) -> EPrim ()
pthreadSigqueue p s word =
  posToUnit $ prim__pthread_sigqueue p.ptr s.sig word
