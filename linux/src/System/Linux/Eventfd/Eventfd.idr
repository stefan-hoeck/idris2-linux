module System.Linux.Eventfd.Eventfd

import Data.C.Ptr
import System.Posix.File.FileDesc

%default total

||| A file descriptor for basic file events.
|||
||| This can be used as an event wait/notify mechanism similar to
||| a `Condition` variable.
export
record Eventfd where
  constructor EFD
  fd : Bits32

export %inline
Cast Eventfd Fd where cast = MkFd . fd

export %inline
Cast CInt Eventfd where cast = EFD . cast
