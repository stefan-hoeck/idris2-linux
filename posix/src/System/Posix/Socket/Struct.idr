module System.Posix.Socket.Struct

import Data.C.Ptr
import System.Posix.File.FileDesc

%default total

||| A file descriptor representing a socket.
export
record Socket where
  constructor S
  fd : Bits32

export %inline
Cast Socket Fd where cast = MkFd . fd

export %inline
Cast CInt Socket where cast = S . cast
