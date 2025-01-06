module System.Posix.Signal.Struct

import Data.C.Ptr
import Data.Finite
import Data.Linear.Traverse1
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

export
InIO SigsetT where

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
sigaddset : (r : SigsetT) -> Signal -> F1 [World] ()
sigaddset (S p) s = ffi $ prim__sigaddset p s.sig

||| Removes a signal from a `sigset_t`
export %inline
sigdelset : (r : SigsetT) -> Signal -> F1 [World] ()
sigdelset (S p) s = ffi $ prim__sigdelset p s.sig

||| Tests if a signal is a member of a `sigset_t`.
export %inline
sigismember : (r : SigsetT) -> Signal -> F1 [World] Bool
sigismember (S p) s t =
  case ffi (prim__sigismember p s.sig) t of
    0 # t => False # t
    _ # t => True # t

||| Extracts the set signals from a `SigsetT`.
export %inline
getSignals : (r : SigsetT) -> F1 [World] (List Signal)
getSignals set = filterM [<] (sigismember set) values

export
withSignals : List Signal -> (SigsetT -> EPrim a) -> EPrim a
withSignals ss f t =
  let sigs # t := toF1 emptySigset t
      _    # t := traverse1_ (\s => sigaddset sigs s) ss t
      R res  t := f sigs t
        | E x t =>
            let _ # t := ioToF1 (freeStruct sigs) t
             in E x t
      _# t := ioToF1 (freeStruct sigs) t
   in R res t

export
withoutSignals : List Signal -> (SigsetT -> EPrim a) -> EPrim a
withoutSignals ss f t =
  let sigs # t := toF1 fullSigset t
      _    # t := traverse1_ (\s => sigdelset sigs s) ss t
      R res  t := f sigs t
        | E x t =>
            let _ # t := ioToF1 (freeStruct sigs) t
             in E x t
      _ # t := ioToF1 (freeStruct sigs) t
   in R res t

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
siginfo : SiginfoT -> F1 [World] Siginfo
siginfo (ST p) t =
  let sig # t := ffi (get_siginfo_t_si_signo p) t
      cod # t := ffi (get_siginfo_t_si_code p) t
      pid # t := ffi (get_siginfo_t_si_pid p) t
      uid # t := ffi (get_siginfo_t_si_uid p) t
      stt # t := ffi (get_siginfo_t_si_status p) t
      val # t := ffi (get_siginfo_t_si_value p) t
   in SI (S sig) cod pid uid stt val # t
