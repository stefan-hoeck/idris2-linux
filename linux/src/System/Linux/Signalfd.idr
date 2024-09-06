module System.Linux.Signalfd

import public Data.C.Ptr
import public System.Linux.Signalfd.Flags
import public System.Posix.File
import public System.Posix.Signal

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_signalfd, linux-idris"
prim__signalfd : AnyPtr -> Bits32 -> PrimIO CInt

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
export
record Signalfd where
  constructor SFD
  fd : Bits32

export %inline
Cast Signalfd Fd where cast = MkFd . fd

||| Opens a new `signalfd` file descriptor for observing the
||| signals specified in the given `SigsetT`.
|||
|||
||| Notes:
||| * Usually, the signals in `set` should first be blocked via `sigprocmask`.
||| * A `signalfd` should be closed using `close` just like other file
|||   descriptors.
||| * In general, used `readSignalfd` instead of the `read` functions
|||   from `System.Posix.File` to read from a `signalfd`.
export %inline
signalfd : (set : SigsetT) -> SignalfdFlags -> IO (Either Errno Signalfd)
signalfd set (F f) = toVal (SFD . cast) $ prim__signalfd (unsafeUnwrap set) f

||| Result type when reading from a `Signalfd`.
export
record SignalfdSiginfo where
  constructor SI
  ptr : AnyPtr

export %inline
Deref SignalfdSiginfo where deref = pure . SI

public export %inline
SizeOf SignalfdSiginfo where sizeof_ = signalfd_siginfo_size

||| The signal that was raised
export %inline
signal : HasIO io => SignalfdSiginfo -> io Signal
signal (SI p) =
  primIO $ \w => let MkIORes s w := prim__ssi_signo p w in MkIORes (S s) w

export %inline
errno : HasIO io => SignalfdSiginfo -> io Int32
errno (SI p) = primIO $ prim__ssi_errno p

export %inline
code : HasIO io => SignalfdSiginfo -> io Int32
code (SI p) = primIO $ prim__ssi_code p

||| ID of the process that raised the signal.
export %inline
pid : HasIO io => SignalfdSiginfo -> io PidT
pid (SI p) = primIO $ prim__ssi_pid p

||| Real user ID of the process that raised the signal.
export %inline
uid : HasIO io => SignalfdSiginfo -> io UidT
uid (SI p) = primIO $ prim__ssi_uid p

||| File descriptor that caught the signal.
export %inline
fd : HasIO io => SignalfdSiginfo -> io Signalfd
fd (SI p) =
  primIO $ \w => let MkIORes s w := prim__ssi_fd p w in MkIORes (SFD s) w

||| ID of the timer that raised the signal.
export %inline
tid : HasIO io => SignalfdSiginfo -> io Bits32
tid (SI p) = primIO $ prim__ssi_tid p

export %inline
band : HasIO io => SignalfdSiginfo -> io Bits32
band (SI p) = primIO $ prim__ssi_band p

export %inline
overrun : HasIO io => SignalfdSiginfo -> io Bits32
overrun (SI p) = primIO $ prim__ssi_overrun p

export %inline
trapno : HasIO io => SignalfdSiginfo -> io Bits32
trapno (SI p) = primIO $ prim__ssi_trapno p

export %inline
status : HasIO io => SignalfdSiginfo -> io Int32
status (SI p) = primIO $ prim__ssi_status p

||| Integer value of a realtime signal.
export %inline
int : HasIO io => SignalfdSiginfo -> io Int32
int (SI p) = primIO $ prim__ssi_int p

||| Pointer value of a realtime signal
export %inline
ptr : HasIO io => SignalfdSiginfo -> io Bits64
ptr (SI p) = primIO $ prim__ssi_ptr p

export %inline
utime : HasIO io => SignalfdSiginfo -> io Bits64
utime (SI p) = primIO $ prim__ssi_utime p

export %inline
stime : HasIO io => SignalfdSiginfo -> io Bits64
stime (SI p) = primIO $ prim__ssi_stime p

export %inline
addr : HasIO io => SignalfdSiginfo -> io Bits64
addr (SI p) = primIO $ prim__ssi_addr p

export %inline
addrlsb : HasIO io => SignalfdSiginfo -> io Bits16
addrlsb (SI p) = primIO $ prim__ssi_addr_lsb p

||| Reads data from a `signalfd` into a pre-allocated array.
|||
||| Note: This will overwrite the data stored in `arr` and the
|||       result is a wrapper around the same pointer.
export
readSignalfd :
     {n : _}
  -> Signalfd
  -> (arr : CArrayIO n SignalfdSiginfo)
  -> IO (Either Errno $ (n ** CArrayIO n SignalfdSiginfo))
readSignalfd fd arr =
  let p  := unsafeUnwrap arr
      sz := sizeof SignalfdSiginfo
   in readPtr fd p (cast $ n * sz) >>= \case
        Left x   => pure (Left x)
        Right bs => pure (Right (cast (bs `div` cast sz) ** unsafeWrap p))
