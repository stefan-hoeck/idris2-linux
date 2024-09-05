module System.Posix.Signal

import System.Callback
import Data.C.Array
import public Data.C.Integer
import public System.Posix.Errno
import public System.Posix.Signal.Types
import public System.Signal

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_kill, posix-idris"
prim__kill : PidT -> CInt -> PrimIO CInt

%foreign "C:raise, posix-idris"
prim__raise : CInt -> PrimIO ()

%foreign "C:li_emptysigset, posix-idris"
prim__emptysigset : PrimIO AnyPtr

%foreign "C:li_fullsigset, posix-idris"
prim__fullsigset : PrimIO AnyPtr

%foreign "C:sigaddset, posix-idris"
prim__sigaddset : AnyPtr -> CInt -> PrimIO ()

%foreign "C:sigdelset, posix-idris"
prim__sigdelset : AnyPtr -> CInt -> PrimIO ()

%foreign "C:sigismember, posix-idris"
prim__sigismember : AnyPtr -> CInt -> PrimIO CInt

%foreign "C:li_sigprocmask1, posix-idris"
prim__sigprocmask1 : Bits8 -> AnyPtr -> PrimIO ()

%foreign "C:li_sigprocmask, posix-idris"
prim__sigprocmask : Bits8 -> AnyPtr -> PrimIO AnyPtr

%foreign "C:li_siggetprocmask, posix-idris"
prim__siggetprocmask : PrimIO AnyPtr

%foreign "C:li_sigpending, posix-idris"
prim__sigpending : PrimIO AnyPtr

%foreign "scheme:(lambda (s f) (register-signal-handler s (lambda (x) ((f x) #f))))"
prim__onsignal : CInt -> (CInt -> PrimIO ()) -> PrimIO ()

%foreign "C:abort, posix-idris"
prim__abort : PrimIO ()

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
sigaddset (S p) s = primIO $ prim__sigaddset p (cast $ signalCode s)

||| Removes a signal from a `sigset_t`
export %inline
sigdelset : HasIO io => SigsetT -> Signal -> io ()
sigdelset (S p) s = primIO $ prim__sigdelset p (cast $ signalCode s)

||| Tests if a signal is a member of a `sigset_t`.
export %inline
sigismember : HasIO io => SigsetT -> Signal -> io Bool
sigismember (S p) s =
  primIO $ \w =>
    let MkIORes r w := prim__sigismember p (cast $ signalCode s) w
     in case r of
          0 => MkIORes False w
          _ => MkIORes True w


--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Sends a signal to a running process or a group of processes.
export %inline
kill : PidT -> Signal -> IO (Either Errno ())
kill p s = toUnit $ prim__kill p (cast $ signalCode s)

||| Sends a signal to the calling thread.
export %inline
raise : Signal -> IO ()
raise s = fromPrim $ prim__raise (cast $ signalCode s)

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

||| Runs the given callback when the given signal is encountered.
|||
||| Note: This is not strictly a POSIX compatible function and is
|||       currently only available on the Scheme backends. It is here
|||       for two reasons: a) We can't safely use Scheme function callbacks
|||       in system interrupts (see the documentation of the Chez FFI)
|||       and therefore can't use C functions `signal` and `sigaction`
|||       with a callback functions calling Scheme code.
|||       b) It is convenient to be able to define simple asynchronous
|||       signal handlers.
export
onsignal : HasIO io => Signal -> (CInt -> IO ()) -> io ()
onsignal s act = primIO $ prim__onsignal (cast $ signalCode s) (\x => toPrim $ act x)

||| Terminates the application by raising `SIGABRT` and dumps core.
|||
||| While `SIGABRT` can be handled with a signal handler, `abort` is
||| still guaranteed successfully terminate the process.
export %inline
abort : HasIO io => io ()
abort = primIO prim__abort
