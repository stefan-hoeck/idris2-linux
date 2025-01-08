module System.Posix.Socket.Struct

import Data.C.Ptr
import System.Posix.Errno
import System.Posix.File.FileDesc
import System.Posix.Socket.Types

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------



--------------------------------------------------------------------------------
-- Socket
--------------------------------------------------------------------------------

||| A file descriptor representing a socket.
export
record Socket (d : Domain) where
  constructor S
  fd : Bits32

export %inline
Cast (Socket d) Fd where cast = MkFd . fd

export %inline
Cast CInt (Socket d) where cast = S . cast

--------------------------------------------------------------------------------
-- SockaddrUn
--------------------------------------------------------------------------------

%foreign "C:li_sockaddr_un, posix-idris"
prim__sockaddr_un: String -> PrimIO AnyPtr

export
record SockaddrUn where
  constructor SUN
  ptr : AnyPtr

export %inline
Struct SockaddrUn where
  wrap   = SUN
  unwrap = ptr

export
InIO SockaddrUn where

export
SizeOf SockaddrUn where
  sizeof_ = sockaddr_un_size

||| Creates a `sockaddr_un` pointer and sets its `sun_path` value to
||| the given path.
|||
||| The allocated memory must be freed via `freeStruct`.
export %inline
sockaddrUn : (path : String) -> F1 [World] SockaddrUn
sockaddrUn path = toF1 $ primMap SUN $ prim__sockaddr_un path
