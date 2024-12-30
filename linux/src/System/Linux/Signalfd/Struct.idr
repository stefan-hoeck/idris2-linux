module System.Linux.Signalfd.Struct

import Data.C.Ptr
import System.Linux.Signalfd.Flags
import System.Posix.File.FileDesc
import System.Posix.Signal.Struct
import System.Posix.Signal.Types

%default total

%foreign "C:li_ssi_signo, linux-idris"
prim__ssi_signo : AnyPtr -> PrimIO Bits32

%foreign "C:li_ssi_errno, linux-idris"
prim__ssi_errno : AnyPtr -> PrimIO Int32

%foreign "C:li_ssi_code, linux-idris"
prim__ssi_code : AnyPtr -> PrimIO Int32

%foreign "C:li_ssi_pid, linux-idris"
prim__ssi_pid : AnyPtr -> PrimIO PidT

%foreign "C:li_ssi_uid, linux-idris"
prim__ssi_uid : AnyPtr -> PrimIO UidT

%foreign "C:li_ssi_fd, linux-idris"
prim__ssi_fd : AnyPtr -> PrimIO Bits32

%foreign "C:li_ssi_tid, linux-idris"
prim__ssi_tid : AnyPtr -> PrimIO Bits32

%foreign "C:li_ssi_band, linux-idris"
prim__ssi_band : AnyPtr -> PrimIO Bits32

%foreign "C:li_ssi_overrun, linux-idris"
prim__ssi_overrun : AnyPtr -> PrimIO Bits32

%foreign "C:li_ssi_trapno, linux-idris"
prim__ssi_trapno : AnyPtr -> PrimIO Bits32

%foreign "C:li_ssi_status, linux-idris"
prim__ssi_status : AnyPtr -> PrimIO Int32

%foreign "C:li_ssi_status, linux-idris"
prim__ssi_int : AnyPtr -> PrimIO Int32

%foreign "C:li_ssi_ptr, linux-idris"
prim__ssi_ptr : AnyPtr -> PrimIO Bits64

%foreign "C:li_ssi_utime, linux-idris"
prim__ssi_utime : AnyPtr -> PrimIO Bits64

%foreign "C:li_ssi_stime, linux-idris"
prim__ssi_stime : AnyPtr -> PrimIO Bits64

%foreign "C:li_ssi_addr, linux-idris"
prim__ssi_addr : AnyPtr -> PrimIO Bits64

%foreign "C:li_ssi_addr_lsb, linux-idris"
prim__ssi_addr_lsb : AnyPtr -> PrimIO Bits16

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| A file descriptor for signal handling.
|||
||| This can be used for synchronous signal handling using
||| (blocking) `readSignalfd` directly, or for asynchronous signal handling
||| using `epoll`.
export
record Signalfd where
  constructor SFD
  fd : Bits32

export %inline
Cast Signalfd Fd where cast = MkFd . fd

export %inline
Cast Bits32 Signalfd where cast = SFD

export %inline
Cast CInt Signalfd where cast = SFD . cast

||| Result type when reading from a `Signalfd`.
export
record SSiginfo where
  constructor SSI
  ptr : AnyPtr

export %inline
Deref SSiginfo where deref = pure . SSI

public export %inline
SizeOf SSiginfo where sizeof_ = signalfd_siginfo_size

export
siginfo : SSiginfo -> PrimIO Siginfo
siginfo (SSI p) w =
  let MkIORes sig w := prim__ssi_signo p w
      MkIORes cod w := prim__ssi_code p w
      MkIORes pid w := prim__ssi_pid p w
      MkIORes uid w := prim__ssi_uid p w
      MkIORes stt w := prim__ssi_status p w
      MkIORes val w := prim__ssi_int p w
   in MkIORes (SI (S sig) cod pid uid stt (cast val)) w
