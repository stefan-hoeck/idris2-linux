module System.Posix.Signal.Struct

import Data.C.Ptr
import Data.Finite
import Derive.Prelude
import System.Posix.Errno
import System.Posix.Signal.Types

%default total
%language ElabReflection

signals : List Signal
signals =
  map Signal.Types.S $
    if SIGRTMAX > 31 then [1..sig SIGRTMAX] else [1..31]

export %inline
Finite Signal where
  values = signals

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

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
-- SigsetT
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

||| Extracts the set signals from a `SigsetT`.
export %inline
getSignals : SigsetT -> PrimIO (List Signal)
getSignals set = filterM [<] (sigismember set) values

export
withSignals : List Signal -> (SigsetT -> EPrim a) -> EPrim a
withSignals ss f w =
  let MkIORes sigs w := emptySigset w
      MkIORes _    w := primTraverse_ (sigaddset sigs) ss w
      R res        w := f sigs w
        | E x w =>
            let MkIORes _ w := toPrim (freeStruct sigs) w
             in E x w
      MkIORes _    w := toPrim (freeStruct sigs) w
   in R res w

export
withoutSignals : List Signal -> (SigsetT -> EPrim a) -> EPrim a
withoutSignals ss f w =
  let MkIORes sigs w := fullSigset w
      MkIORes _    w := primTraverse_ (sigdelset sigs) ss w
      R res        w := f sigs w
        | E x w =>
            let MkIORes _ w := toPrim (freeStruct sigs) w
             in E x w
      MkIORes _    w := toPrim (freeStruct sigs) w
   in R res w

--------------------------------------------------------------------------------
-- Siginfo
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
