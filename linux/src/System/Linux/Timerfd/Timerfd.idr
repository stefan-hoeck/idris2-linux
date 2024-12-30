module System.Linux.Timerfd.Timerfd

import Data.C.Ptr
import public System.Posix.File.FileDesc

%default total

||| A file descriptor for signal handling.
|||
||| This can be used for synchronous signal handling using
||| (blocking) `readSignalfd` directly, or for asynchronous signal handling
||| using `epoll`.
export
record Timerfd where
  constructor TFD
  fd : Bits32

export %inline
Cast Timerfd Fd where cast = MkFd . fd

export %inline
Cast Bits32 Timerfd where cast = TFD

export %inline
Cast CInt Timerfd where cast = TFD . cast
