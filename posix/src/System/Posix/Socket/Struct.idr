module System.Posix.Socket.Struct

import Data.C.Ptr
import System.Posix.Errno
import System.Posix.File.FileDesc
import System.Posix.Socket.Types

%default total

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

--------------------------------------------------------------------------------
-- SockaddrIn
--------------------------------------------------------------------------------

public export
record IPv4Address where
  constructor I4
  addr : Bits32

%foreign "C:li_sockaddr_in, posix-idris"
prim__sockaddr_in: Bits32 -> Bits16 -> PrimIO AnyPtr

export
record SockaddrIn where
  constructor SIN
  ptr : AnyPtr

export %inline
Struct SockaddrIn where
  wrap   = SIN
  unwrap = ptr

export
InIO SockaddrIn where

export
SizeOf SockaddrIn where
  sizeof_ = sockaddr_in_size

||| Creates a `sockaddr_in` pointer and sets its `sun_path` value to
|||
||| The allocated memory must be freed via `freeStruct`.
export %inline
sockaddrIn : (addr : IPv4Address) -> Bits16 -> F1 [World] SockaddrIn
sockaddrIn (I4 addr) port = toF1 $ primMap SIN $ prim__sockaddr_in addr port

--------------------------------------------------------------------------------
-- SockaddrIn6
--------------------------------------------------------------------------------

export
record SockaddrIn6 where
  constructor SIN6
  ptr : AnyPtr

export %inline
Struct SockaddrIn6 where
  wrap   = SIN6
  unwrap = ptr

export
InIO SockaddrIn6 where

export
SizeOf SockaddrIn6 where
  sizeof_ = sockaddr_in6_size

public export
0 Sockaddr : Domain -> Type
Sockaddr AF_UNIX  = SockaddrUn
Sockaddr AF_INET  = SockaddrIn
Sockaddr AF_INET6 = SockaddrIn6

export
ptr : (d : _) -> Sockaddr d -> AnyPtr
ptr AF_UNIX  x = x.ptr
ptr AF_INET  x = x.ptr
ptr AF_INET6 x = x.ptr

export
addrSize : (d : Domain) -> Bits32
addrSize AF_UNIX  = sizeof SockaddrUn
addrSize AF_INET  = sizeof SockaddrIn
addrSize AF_INET6 = sizeof SockaddrIn6

