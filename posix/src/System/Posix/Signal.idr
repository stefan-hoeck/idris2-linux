module System.Posix.Signal

import Data.C.Ptr

import public Data.C.Integer
import public System.Posix.Errno
import public System.Posix.Signal.Types

%default total

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

%foreign "C:abort, posix-idris"
prim__abort : PrimIO ()

%foreign "C:li_sigqueue, posix-idris"
prim__sigqueue : PidT -> Bits32 -> CInt -> PrimIO CInt

%foreign "C:li_pause, posix-idris"
prim__pause : PrimIO CInt

%foreign "C:li_sigsuspend, posix-idris"
prim__sigsuspend : AnyPtr -> PrimIO CInt

%foreign "C:li_si_signo, posix-idris"
prim__signo : AnyPtr -> PrimIO Bits32

%foreign "C:li_si_signo, posix-idris"
prim__code : AnyPtr -> PrimIO CInt

%foreign "C:li_si_pid, posix-idris"
prim__pid : AnyPtr -> PrimIO PidT

%foreign "C:li_si_uid, posix-idris"
prim__uid : AnyPtr -> PrimIO UidT

%foreign "C:li_si_status, posix-idris"
prim__status : AnyPtr -> PrimIO CInt

%foreign "C:li_si_value, posix-idris"
prim__value : AnyPtr -> PrimIO CInt

%foreign "C:li_sigwaitinfo, posix-idris"
prim__sigwaitinfo : AnyPtr -> AnyPtr -> PrimIO CInt

%foreign "C:li_sigtimedwait, posix-idris"
prim__sigtimedwait : AnyPtr -> AnyPtr -> TimeT -> NsecT -> PrimIO CInt


--------------------------------------------------------------------------------
-- Signal Sets
--------------------------------------------------------------------------------

||| Wrapper around a pointer of a signal set (`sigset_t`).
export
record SigsetT where
  constructor S
  ptr : AnyPtr

||| Allocates a `sigset_t` with all signals cleared.
|||
||| This must be freed with `freeSigset`.
export %inline
emptySigset : HasIO io => io SigsetT
emptySigset =
  primIO $ \w => let MkIORes p w := prim__emptysigset w in MkIORes (S p) w

||| Allocates a `sigset_t` with all signals set.
|||
||| This must be freed with `freeSigset`.
export %inline
fullSigset : HasIO io => io SigsetT
fullSigset =
  primIO $ \w => let MkIORes p w := prim__fullsigset w in MkIORes (S p) w

||| Frees the allocated pointer of a `sigset_t`.
export %inline
freeSigset : HasIO io => SigsetT -> io ()
freeSigset (S p) = primIO $ prim__free p

||| Adds a signal to a `sigset_t`
export %inline
sigaddset : HasIO io => SigsetT -> Signal -> io ()
sigaddset (S p) s = primIO $ prim__sigaddset p s.sig

||| Removes a signal from a `sigset_t`
export %inline
sigdelset : HasIO io => SigsetT -> Signal -> io ()
sigdelset (S p) s = primIO $ prim__sigdelset p s.sig

||| Tests if a signal is a member of a `sigset_t`.
export %inline
sigismember : HasIO io => SigsetT -> Signal -> io Bool
sigismember (S p) s =
  primIO $ \w =>
    let MkIORes r w := prim__sigismember p s.sig w
     in case r of
          0 => MkIORes False w
          _ => MkIORes True w

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Sends a signal to a running process or a group of processes.
export %inline
kill : PidT -> Signal -> IO (Either Errno ())
kill p s = toUnit $ prim__kill p s.sig

||| Sends a signal to the calling thread.
export %inline
raise : Signal -> IO ()
raise s = fromPrim $ prim__raise s.sig

||| Sends a realtime signal plus data word to a running process.
|||
||| Note that `sig` must be in the range [SIGRTMIN, SIGRTMAX].
export %inline
sigqueue : PidT -> Signal -> (word : CInt) -> IO (Either Errno ())
sigqueue p s word = toUnit $ prim__sigqueue p s.sig word

||| Adjust the process signal mask according to the given `How`
||| and signal set.
|||
||| Note: This allocates a new `sigset_t` pointer and returns the
|||       previously set signal mask. Client code is responsible to
|||       free the memory for this once it is no longer used.
|||       See also `sigprocmask'` for a version that does not return
|||       the previous signal mask.
export %inline
sigprocmask : HasIO io => How -> SigsetT -> io SigsetT
sigprocmask h (S p) =
  primIO $ \w =>
    let MkIORes p2 w := prim__sigprocmask (howCode h) p w
     in MkIORes (S p2) w

||| Like `sigprocmask` but does not allocate a pointer for the
||| previous `sigset_t`.
export %inline
sigprocmask' : HasIO io => How -> SigsetT -> io ()
sigprocmask' h (S p) = primIO $ prim__sigprocmask1 (howCode h) p

||| Returns the current signal mask of the process.
|||
||| Note: This allocates a new `sigset_t` pointer and returns the
|||       previously set signal mask. Client code is responsible to
|||       free the memory for this once it is no longer used.
export %inline
siggetprocmask : HasIO io => io SigsetT
siggetprocmask =
  primIO $ \w =>
    let MkIORes p w := prim__siggetprocmask w
     in MkIORes (S p) w

||| Returns the set of currently pending signals.
|||
||| Note: This allocates a new `sigset_t` pointer and returns the
|||       previously set signal mask. Client code is responsible to
|||       free the memory for this once it is no longer used.
export %inline
sigpending : HasIO io => io SigsetT
sigpending =
  primIO $ \w =>
    let MkIORes p w := prim__sigpending w
     in MkIORes (S p) w

||| Terminates the application by raising `SIGABRT` and dumps core.
|||
||| While `SIGABRT` can be handled with a signal handler, `abort` is
||| still guaranteed successfully terminate the process.
export %inline
abort : HasIO io => io ()
abort = primIO prim__abort

||| Suspends the current thread until a non-blocked signal is encountered.
export %inline
pause : IO (Either Errno ())
pause =
  toUnit prim__pause >>= \case
    Left EINTR => pure $ Right () -- this is the normal case
    x          => pure x

--------------------------------------------------------------------------------
-- Synchronous Signal Handling
--------------------------------------------------------------------------------

export
record SiginfoT where
  constructor ST
  ptr : AnyPtr

||| Allocates a `SiginfoT` pointer.
|||
||| The allocated memory must be freed via `freeSiginfoT`.
export %inline
allocSiginfoT : HasIO io => io SiginfoT
allocSiginfoT = primIO $ MkIORes (ST $ prim__malloc siginfo_t_size)

||| Frees the memory allocated for a `SiginfoT` pointer.
export %inline
freeSiginfoT : HasIO io => SiginfoT -> io ()
freeSiginfoT (ST p) = primIO $ prim__free p

||| The signal that let to the current event.
export %inline
signal : HasIO io => SiginfoT -> io Signal
signal (ST p) =
  primIO $ \w => let MkIORes v w := prim__signo p w in MkIORes (S v) w

export %inline
code : HasIO io => SiginfoT -> io CInt
code (ST p) = primIO $ prim__code p

||| ID of the process that sent the signal.
export %inline
pid : HasIO io => SiginfoT -> io PidT
pid (ST p) = primIO $ prim__pid p

||| Real user ID of the process that sent the signal.
export %inline
uid : HasIO io => SiginfoT -> io UidT
uid (ST p) = primIO $ prim__uid p

||| Effective user ID of the process that sent the signal.
export %inline
status : HasIO io => SiginfoT -> io CInt
status (ST p) = primIO $ prim__status p

||| Value associated with a realtime signal.
export %inline
value : HasIO io => SiginfoT -> io CInt
value (ST p) = primIO $ prim__value p

||| Atomically blocks all signals not in `set`, then
||| pauses the thread (see `pause`) and restores the signal set
||| afterwards.
export %inline
sigsuspend : (set : SigsetT) -> IO (Either Errno ())
sigsuspend (S s) =
  toUnit (prim__sigsuspend s) >>= \case
    Left EINTR => pure $ Right () -- this is the normal case
    x          => pure x

||| Synchronously awaits one of the signals in `set`.
|||
||| Note: Usually, the signals in `set` should first be blocked via
|||       `sigprocmask`.
export %inline
sigwaitinfo : (set : SigsetT) -> (info : SiginfoT) -> IO (Either Errno ())
sigwaitinfo (S s) (ST i) = toUnit $ prim__sigwaitinfo s i

||| Like `sigwaitinfo` but times out with `EAGAIN` after `sec` seconds and
||| `nsec` nanoseconds.
export %inline
sigtimedwait :
     (set  : SigsetT)
  -> (info : SiginfoT)
  -> (sec  : TimeT)
  -> (nsec : NsecT)
  -> IO (Either Errno ())
sigtimedwait (S s) (ST i) sec nsec = toUnit $ prim__sigtimedwait s i sec nsec
