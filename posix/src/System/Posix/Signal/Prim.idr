module System.Posix.Signal.Prim

import Data.C.Ptr
import Data.Finite

import public Data.C.Integer
import public Data.C.Struct
import public System.Posix.Errno
import public System.Posix.Signal.Struct
import public System.Posix.Signal.Types

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_kill, posix-idris"
prim__kill : PidT -> Bits32 -> PrimIO CInt

%foreign "C:raise, posix-idris"
prim__raise : Bits32 -> PrimIO ()

%foreign "C:li_sigprocmask1, posix-idris"
prim__sigprocmask1 : Bits8 -> AnyPtr -> PrimIO ()

%foreign "C:li_sigprocmask, posix-idris"
prim__sigprocmask : Bits8 -> AnyPtr -> PrimIO AnyPtr

%foreign "C:li_siggetprocmask, posix-idris"
prim__siggetprocmask : PrimIO AnyPtr

%foreign "C:li_sigpending, posix-idris"
prim__sigpending : PrimIO AnyPtr

%foreign "C:li_sigqueue, posix-idris"
prim__sigqueue : PidT -> Bits32 -> CInt -> PrimIO CInt

%foreign "C:li_pause, posix-idris"
prim__pause : PrimIO CInt

%foreign "C:li_sigsuspend, posix-idris"
prim__sigsuspend : AnyPtr -> PrimIO CInt

%foreign "C:li_sigwaitinfo, posix-idris"
prim__sigwaitinfo : AnyPtr -> AnyPtr -> PrimIO CInt

%foreign "C:li_sigtimedwait, posix-idris"
prim__sigtimedwait : AnyPtr -> AnyPtr -> TimeT -> NsecT -> PrimIO CInt

%foreign "C:li_sigwait, posix-idris"
prim__sigwait : AnyPtr -> PrimIO CInt

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Sends a signal to a running process or a group of processes.
export %inline
kill : PidT -> Signal -> EPrim ()
kill p s = toUnit $ prim__kill p s.sig

||| Sends a signal to the calling thread.
export %inline
raise : Signal -> PrimIO ()
raise s = prim__raise s.sig

||| Sends a realtime signal plus data word to a running process.
|||
||| Note that `sig` must be in the range [SIGRTMIN, SIGRTMAX].
export %inline
sigqueue : PidT -> Signal -> (word : CInt) -> EPrim ()
sigqueue p s word = toUnit $ prim__sigqueue p s.sig word

||| Adjust the process signal mask according to the given `How`
||| and signal set.
|||
||| Note: This allocates a new `sigset_t` pointer and returns the
|||       previously set signal mask. Client code is responsible to
|||       free the memory for this once it is no longer used.
|||       See also `sigprocmask` for a version that does not return
|||       the previous signal mask.
export %inline
sigprocmask_ : How -> SigsetT -> PrimIO SigsetT
sigprocmask_ h p w =
  let MkIORes p2 w := prim__sigprocmask (howCode h) (unwrap p) w
   in MkIORes (wrap p2) w

||| Terminates the application by raising `SIGABRT` and dumps core.
|||
||| While `SIGABRT` can be handled with a signal handler, `abort` is
||| still guaranteed successfully terminate the process.
export %foreign "C:abort, posix-idris"
abort : PrimIO ()

||| Suspends the current thread until a non-blocked signal is encountered.
export %inline
pause : EPrim ()
pause t =
  let r # t := toF1 (primMap fromNeg prim__pause) t
   in if r == EINTR then R () t else E (inject r) t

||| Atomically blocks the signals in `set`, then
||| pauses the thread (see `pause`) and restores the signal set
||| afterwards.
export %inline
sigsuspend_ : (set : SigsetT) -> EPrim ()
sigsuspend_ s t =
  let r # t := toF1 (primMap fromNeg (prim__sigsuspend $ unwrap s)) t
   in if r == EINTR then R () t else E (inject r) t

||| Synchronously awaits one of the signals in `set`.
|||
||| Note: Usually, the signals in `set` should first be blocked via
|||       `sigprocmask`.
export %inline
sigwaitinfo_ : (set : SigsetT) -> (info : SiginfoT) -> EPrim ()
sigwaitinfo_ s i = toUnit $ prim__sigwaitinfo (unwrap s) (unwrap i)

||| Synchronously awaits one of the signals in `set`.
|||
||| This is like `sigwaitinfo` but with a simpler API.
export %inline
sigwait_ : (set : SigsetT) -> EPrim Signal
sigwait_ s = toVal (S . cast) $ prim__sigwait (unwrap s)

||| Like `sigwaitinfo` but times out with `EAGAIN` after `sec` seconds and
||| `nsec` nanoseconds.
export %inline
sigtimedwait :
     (set  : SigsetT)
  -> (info : SiginfoT)
  -> (sec  : TimeT)
  -> (nsec : NsecT)
  -> EPrim ()
sigtimedwait s i sec nsec =
  toUnit $ prim__sigtimedwait (unwrap s) (unwrap i) sec nsec

--------------------------------------------------------------------------------
-- Convenience API
--------------------------------------------------------------------------------

||| Like `sigprocmask_` but does not allocate a pointer for the
||| previous `sigset_t`.
export %inline
sigprocmask : How -> List Signal -> EPrim ()
sigprocmask h ss =
  withSignals ss $ \p,t =>
    let _ # t := toF1 (prim__sigprocmask1 (howCode h) (unwrap p)) t
     in R () t

||| Returns the current signal mask of the process.
export %inline
siggetprocmask : PrimIO (List Signal)
siggetprocmask w =
  let MkIORes p  w := prim__siggetprocmask w
      MkIORes ss w := primRun (getSignals (wrap p)) w
      MkIORes _  w := prim__free p w
   in MkIORes ss w

||| Returns the set of currently pending signals.
export %inline
sigpending : PrimIO (List Signal)
sigpending w =
  let MkIORes p  w := prim__sigpending w
      MkIORes ss w := primRun (getSignals (wrap p)) w
      MkIORes _  w := prim__free p w
   in MkIORes ss w

||| Convenience alias for `sigsuspend_`
export %inline
sigsuspend : List Signal -> EPrim ()
sigsuspend ss = withSignals ss sigsuspend_

||| Convenience alias for `sigwait_`.
export %inline
sigwait : List Signal -> EPrim Signal
sigwait ss = withSignals ss sigwait_

||| Convenience alias for `sigwaitinfo_`.
export
sigwaitinfo : List Signal -> EPrim Siginfo
sigwaitinfo ss =
  withSignals ss $ \set => withStruct SSiginfoT $ \si,t =>
    let R _ t := sigwaitinfo_ set si t | E x t => E x t
        r # t := siginfo si t
     in R r t
