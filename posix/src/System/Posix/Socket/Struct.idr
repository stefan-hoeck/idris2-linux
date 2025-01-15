module System.Posix.Socket.Struct

import Data.Bits
import Data.C.Ptr
import Data.Vect
import Derive.Prelude
import System.Posix.Errno
import System.Posix.File.FileDesc
import System.Posix.Socket.Types

%default total
%language ElabReflection

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

%foreign "C:sockaddr_un_path, posix-idris"
prim__sockaddr_un_path: AnyPtr -> PrimIO String

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

export %inline
path : SockaddrUn -> F1 [World] String
path (SUN p) = toF1 $ prim__sockaddr_un_path p

--------------------------------------------------------------------------------
-- SockaddrIn
--------------------------------------------------------------------------------

%foreign "C:li_sockaddr_in, posix-idris"
prim__sockaddr_in: Bits32 -> Bits16 -> PrimIO AnyPtr

%foreign "C:sockaddr_in_port, posix-idris"
prim__sockaddr_in_port: AnyPtr -> PrimIO Bits16

%foreign "C:sockaddr_in_addr, posix-idris"
prim__sockaddr_in_addr: AnyPtr -> PrimIO Bits32

%foreign "C:sockaddr_in_addr_str, posix-idris"
prim__sockaddr_in_addr_str: AnyPtr -> PrimIO String

public export
record IP4Addr where
  constructor IP4
  addr : Vect 4 Bits8
  port : Bits16

%runElab derive "IP4Addr" [Show,Eq]

export
ip4addr : Vect 4 Bits8 -> Bits32
ip4addr [w,x,y,z] =
  shiftL (cast w) 24 .|. shiftL (cast x) 16 .|. shiftL (cast y) 8 .|. cast z

export
splitIp4Addr : Bits32 -> Vect 4 Bits8
splitIp4Addr x =
  [cast (shiftR x 24), cast (shiftR x 16), cast (shiftR x 8), cast x]

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

namespace SockaddrIn
  export %inline
  port : SockaddrIn -> F1 [World] Bits16
  port (SIN p) = ffi $ prim__sockaddr_in_port p

  export %inline
  addr : SockaddrIn -> F1 [World] Bits32
  addr (SIN p) = ffi $ prim__sockaddr_in_addr p

  export %inline
  addrStr : SockaddrIn -> F1 [World] String
  addrStr (SIN p) = ffi $ prim__sockaddr_in_addr_str p

||| Creates a `sockaddr_in` pointer and sets its `sun_path` value to
|||
||| The allocated memory must be freed via `freeStruct`.
export %inline
sockaddrIn : IP4Addr -> F1 [World] SockaddrIn
sockaddrIn (IP4 a p) = toF1 $ primMap SIN $ prim__sockaddr_in (ip4addr a) p

--------------------------------------------------------------------------------
-- SockaddrIn6
--------------------------------------------------------------------------------

%foreign "C:li_sockaddr_in6, posix-idris"
prim__sockaddr_in6: Bits16 -> PrimIO AnyPtr

%foreign "C:sockaddr_in6_port, posix-idris"
prim__sockaddr_in6_port: AnyPtr -> PrimIO Bits16

%foreign "C:sockaddr_in6_addr, posix-idris"
prim__sockaddr_in6_addr: AnyPtr -> AnyPtr

%foreign "C:sockaddr_in6_addr_str, posix-idris"
prim__sockaddr_in6_addr_str: AnyPtr -> PrimIO String

public export
record IP6Addr where
  constructor IP6
  addr : Vect 16 Bits8
  port : Bits16

%runElab derive "IP6Addr" [Show,Eq]

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

namespace SockaddrIn6
  export %inline
  port : SockaddrIn6 -> F1 [World] Bits16
  port (SIN6 p) = ffi $ prim__sockaddr_in6_port p

  export %inline
  addr6 : SockaddrIn6 -> CArrayIO 16 Bits8
  addr6 (SIN6 p) = unsafeWrap (prim__sockaddr_in6_addr p)

  export %inline
  addrStr : SockaddrIn6 -> F1 [World] String
  addrStr (SIN6 p) = ffi $ prim__sockaddr_in6_addr_str p

||| Creates a `sockaddr_in` pointer and sets its `sun_path` value to
|||
||| The allocated memory must be freed via `freeStruct`.
export
sockaddrIn6 : IP6Addr -> F1 [World] SockaddrIn6
sockaddrIn6 (IP6 addr pr) t =
  let res # t := toF1 (prim__sockaddr_in6 pr) t
      _   # t := writeVect (addr6 $ SIN6 res) addr t
   in SIN6 res # t

--------------------------------------------------------------------------------
-- Conversions
--------------------------------------------------------------------------------

public export
0 Sockaddr : Domain -> Type
Sockaddr AF_UNIX  = SockaddrUn
Sockaddr AF_INET  = SockaddrIn
Sockaddr AF_INET6 = SockaddrIn6

public export
0 Addr : Domain -> Type
Addr AF_UNIX  = String
Addr AF_INET  = IP4Addr
Addr AF_INET6 = IP6Addr

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

export
sockaddr : (d : _) -> Addr d -> F1 [World] (Sockaddr d)
sockaddr AF_UNIX  a = sockaddrUn a
sockaddr AF_INET  a = sockaddrIn a
sockaddr AF_INET6 a = sockaddrIn6 a
