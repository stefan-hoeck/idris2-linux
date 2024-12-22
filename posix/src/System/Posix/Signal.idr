module System.Posix.Signal

import Data.C.Ptr
import Data.Finite
import Derive.Prelude

import public Data.C.Integer
import public Data.C.Struct
import public System.Posix.Errno
import public System.Posix.Signal.Types

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_kill, posix-idris"
prim__kill : PidT -> Bits32 -> PrimIO CInt

%foreign "C:raise, posix-idris"
prim__raise : Bits32 -> PrimIO ()

%foreign "C:li_emptysigset, posix-idris"
prim__emptysigset : PrimIO AnyPtr

%foreign "C:li_fullsigset, posix-idris"
prim__fullsigset : PrimIO AnyPtr

%foreign "C:sigaddset, posix-idris"
prim__sigaddset : AnyPtr -> Bits32 -> PrimIO ()

%foreign "C:sigdelset, posix-idris"
prim__sigdelset : AnyPtr -> Bits32 -> PrimIO ()

%foreign "C:sigismember, posix-idris"
prim__sigismember : AnyPtr -> Bits32 -> PrimIO CInt

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

export %foreign "C:get_siginfo_t_si_signo, posix-idris"
get_siginfo_t_si_signo: AnyPtr -> PrimIO Bits32

export %foreign "C:get_siginfo_t_si_code, posix-idris"
get_siginfo_t_si_code: AnyPtr -> PrimIO CInt

export %foreign "C:get_siginfo_t_si_pid, posix-idris"
get_siginfo_t_si_pid: AnyPtr -> PrimIO PidT

export %foreign "C:get_siginfo_t_si_uid, posix-idris"
get_siginfo_t_si_uid: AnyPtr -> PrimIO UidT

export %foreign "C:get_siginfo_t_si_status, posix-idris"
get_siginfo_t_si_status: AnyPtr -> PrimIO CInt

export %foreign "C:get_siginfo_t_si_value, posix-idris"
get_siginfo_t_si_value: AnyPtr -> PrimIO CInt

--------------------------------------------------------------------------------
-- Signal Sets
--------------------------------------------------------------------------------

||| Wrapper around a pointer of a signal set (`sigset_t`).
export
record SigsetT where
  constructor S
  ptr : AnyPtr

export %inline
Struct SigsetT where
  wrap   = S
  unwrap = ptr

||| Allocates a `sigset_t` with all signals cleared.
|||
||| This must be freed with `freeSigset`.
export %inline
emptySigset : PrimIO SigsetT
emptySigset = primMap S prim__emptysigset

||| Allocates a `sigset_t` with all signals set.
|||
||| This must be freed with `freeSigset`.
export %inline
fullSigset : PrimIO SigsetT
fullSigset = primMap S prim__fullsigset

||| Adds a signal to a `sigset_t`
export %inline
sigaddset : SigsetT -> Signal -> PrimIO ()
sigaddset (S p) s = prim__sigaddset p s.sig

||| Removes a signal from a `sigset_t`
export %inline
sigdelset : SigsetT -> Signal -> PrimIO ()
sigdelset (S p) s = prim__sigdelset p s.sig

||| Tests if a signal is a member of a `sigset_t`.
export %inline
sigismember : SigsetT -> Signal -> PrimIO Bool
sigismember (S p) s w =
  let MkIORes r w := prim__sigismember p s.sig w
   in case r of
        0 => MkIORes False w
        _ => MkIORes True w

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Sends a signal to a running process or a group of processes.
export %inline
kill : PidT -> Signal -> PrimIO (Either Errno ())
kill p s = toUnit $ prim__kill p s.sig

||| Sends a signal to the calling thread.
export %inline
raise : Signal -> PrimIO ()
raise s = prim__raise s.sig

||| Sends a realtime signal plus data word to a running process.
|||
||| Note that `sig` must be in the range [SIGRTMIN, SIGRTMAX].
export %inline
sigqueue : PidT -> Signal -> (word : CInt) -> PrimIO (Either Errno ())
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
sigprocmask_ h (S p) w =
  let MkIORes p2 w := prim__sigprocmask (howCode h) p w
   in MkIORes (S p2) w

||| Terminates the application by raising `SIGABRT` and dumps core.
|||
||| While `SIGABRT` can be handled with a signal handler, `abort` is
||| still guaranteed successfully terminate the process.
export %foreign "C:abort, posix-idris"
abort : PrimIO ()

||| Suspends the current thread until a non-blocked signal is encountered.
export %inline
pause : PrimIO (Either Errno ())
pause w =
  let MkIORes r w := primMap fromNeg prim__pause w
   in MkIORes (if r == EINTR then Right () else Left r) w

--------------------------------------------------------------------------------
-- Synchronous Signal Handling
--------------------------------------------------------------------------------

export
record SiginfoT where
  constructor ST
  ptr : AnyPtr

export %inline
Struct SiginfoT where
  wrap   = ST
  unwrap = ptr

export %inline
SizeOf SiginfoT where
  sizeof_ = siginfo_t_size

public export
record Siginfo where
  constructor SI
  signal : Signal
  code   : CInt
  pid    : PidT
  uid    : UidT
  status : CInt
  value  : CInt

%runElab derive "Siginfo" [Show,Eq]

export
siginfo : SiginfoT -> PrimIO Siginfo
siginfo (ST p) w =
  let MkIORes sig w := get_siginfo_t_si_signo p w
      MkIORes cod w := get_siginfo_t_si_code p w
      MkIORes pid w := get_siginfo_t_si_pid p w
      MkIORes uid w := get_siginfo_t_si_uid p w
      MkIORes stt w := get_siginfo_t_si_status p w
      MkIORes val w := get_siginfo_t_si_value p w
   in MkIORes (SI (S sig) cod pid uid stt val) w

||| Atomically blocks the signals in `set`, then
||| pauses the thread (see `pause`) and restores the signal set
||| afterwards.
export %inline
sigsuspend_ : (set : SigsetT) -> PrimIO (Either Errno ())
sigsuspend_ (S s) w =
  let MkIORes r w := primMap fromNeg (prim__sigsuspend s) w
   in MkIORes (if r == EINTR then Right () else Left r) w

||| Synchronously awaits one of the signals in `set`.
|||
||| Note: Usually, the signals in `set` should first be blocked via
|||       `sigprocmask`.
export %inline
sigwaitinfo_ : (set : SigsetT) -> (info : SiginfoT) -> PrimIO (Either Errno ())
sigwaitinfo_ (S s) (ST i) = toUnit $ prim__sigwaitinfo s i

||| Synchronously awaits one of the signals in `set`.
|||
||| This is like `sigwaitinfo` but with a simpler API.
export %inline
sigwait_ : (set : SigsetT) -> PrimIO (Either Errno Signal)
sigwait_ (S s) = toVal (S . cast) $ prim__sigwait s

||| Like `sigwaitinfo` but times out with `EAGAIN` after `sec` seconds and
||| `nsec` nanoseconds.
export %inline
sigtimedwait :
     (set  : SigsetT)
  -> (info : SiginfoT)
  -> (sec  : TimeT)
  -> (nsec : NsecT)
  -> PrimIO (Either Errno ())
sigtimedwait (S s) (ST i) sec nsec = toUnit $ prim__sigtimedwait s i sec nsec

--------------------------------------------------------------------------------
-- Convenience API
--------------------------------------------------------------------------------

export
Finite Signal where
  values =
    map Signal.Types.S $
      [1..8] ++ [10..15] ++ [17..27] ++ [29,31] ++ [sig SIGRTMIN .. sig SIGRTMAX]

||| Extracts the set signals from a `SigsetT`.
export %inline
getSignals : SigsetT -> PrimIO (List Signal)
getSignals set = filterM [<] (sigismember set) values

export
withSignals : List Signal -> (SigsetT -> PrimIO a) -> PrimIO a
withSignals ss f w =
  let MkIORes sigs w := emptySigset w
      MkIORes _    w := primTraverse_ (sigaddset sigs) ss w
      MkIORes res  w := f sigs w
      MkIORes _    w := toPrim (freeStruct sigs) w
   in MkIORes res w

export
withoutSignals : List Signal -> (SigsetT -> PrimIO a) -> PrimIO a
withoutSignals ss f w =
  let MkIORes sigs w := fullSigset w
      MkIORes _    w := primTraverse_ (sigdelset sigs) ss w
      MkIORes res  w := f sigs w
      MkIORes _    w := toPrim (freeStruct sigs) w
   in MkIORes res w

||| Like `sigprocmask_` but does not allocate a pointer for the
||| previous `sigset_t`.
export %inline
sigprocmask : How -> List Signal -> PrimIO ()
sigprocmask h ss =
  withSignals ss $ \(S p) => prim__sigprocmask1 (howCode h) p

||| Returns the current signal mask of the process.
export %inline
siggetprocmask : PrimIO (List Signal)
siggetprocmask w =
  let MkIORes p  w := prim__siggetprocmask w
      MkIORes ss w := getSignals (S p) w
      MkIORes _  w := toPrim (freeStruct $ S p) w
   in MkIORes ss w

||| Returns the set of currently pending signals.
export %inline
sigpending : PrimIO (List Signal)
sigpending w =
  let MkIORes p  w := prim__sigpending w
      MkIORes ss w := getSignals (S p) w
      MkIORes _  w := toPrim (freeStruct $ S p) w
   in MkIORes ss w

||| Convenience alias for `sigsuspend_`
export %inline
sigsuspend : List Signal -> PrimIO (Either Errno ())
sigsuspend ss = withSignals ss sigsuspend_

||| Convenience alias for `sigwait_`.
export %inline
sigwait : List Signal -> PrimIO (Either Errno Signal)
sigwait ss = withSignals ss sigwait_

||| Convenience alias for `sigwaitinfo_`.
export
sigwaitinfo : List Signal -> PrimIO (Either Errno Siginfo)
sigwaitinfo ss =
  withSignals ss $ \set => withStruct SiginfoT $ \si,w =>
    let MkIORes (Right _) w := sigwaitinfo_ set si w
          | MkIORes (Left x) w => MkIORes (Left x) w
        MkIORes res       w := siginfo si w
     in MkIORes (Right res) w
