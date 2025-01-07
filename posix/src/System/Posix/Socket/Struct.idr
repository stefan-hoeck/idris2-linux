module System.Posix.Socket.Struct

import Data.C.Ptr
import System.Posix.File.FileDesc
import System.Posix.Socket.Types

%default total

||| A file descriptor representing a socket.
export
record Socket (d : Domain) where
  constructor S
  fd : Bits32

export %inline
Cast (Socket d) Fd where cast = MkFd . fd

export %inline
Cast CInt (Socket d) where cast = S . cast
