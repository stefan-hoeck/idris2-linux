module System.Posix.Signal

import Data.C.Array
import public Data.C.Integer
import public System.Posix.Errno
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
