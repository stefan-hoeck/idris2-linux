module System.Posix.Socket.Prim

import System.Posix.File.Prim

import public Data.Buffer
import public Data.Buffer.Core
import public Data.ByteString
import public Data.ByteVect
import public Data.C.Ptr
import public System.Posix.Errno
import public System.Posix.File.FileDesc
import public System.Posix.File.ReadRes
import public System.Posix.Socket.Struct
import public System.Posix.Socket.Types

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_socket, posix-idris"
prim__socket : Bits8 -> Bits32 -> PrimIO CInt

%foreign "C:li_bind, posix-idris"
prim__bind : Bits32 -> AnyPtr -> Bits32 -> PrimIO CInt

%foreign "C:li_connect, posix-idris"
prim__connect : Bits32 -> AnyPtr -> Bits32 -> PrimIO CInt

%foreign "C:li_listen, posix-idris"
prim__listen : Bits32 -> Bits32 -> PrimIO CInt

%foreign "C:li_accept, posix-idris"
prim__accept : Bits32 -> PrimIO CInt

%foreign "C__collect_safe:li_recv, posix-idris"
prim__recvptr : (file : Bits32) -> AnyPtr -> (max : Bits32) -> Bits32 -> PrimIO SsizeT

%foreign "C:li_recv, posix-idris"
prim__recv : (file : Bits32) -> Buffer -> (max : Bits32) -> Bits32 -> PrimIO SsizeT

%foreign "C__collect_safe:li_recvfrom, posix-idris"
prim__recvfromptr : (file : Bits32) -> AnyPtr -> (max : Bits32) -> Bits32 -> AnyPtr -> Bits32 -> PrimIO SsizeT

%foreign "C:li_recvfrom, posix-idris"
prim__recvfrom : (file : Bits32) -> Buffer -> (max : Bits32) -> Bits32 -> AnyPtr -> Bits32 -> PrimIO SsizeT

%foreign "C:li_sendto, posix-idris"
prim__sendto : (file : Bits32) -> Buffer -> (off,max : Bits32) -> Bits32 -> AnyPtr -> Bits32 -> PrimIO SsizeT

%foreign "C__collect_safe:li_sendto, posix-idris"
prim__sendtoptr : (file : Bits32) -> AnyPtr -> (off,max : Bits32) -> Bits32 -> AnyPtr -> Bits32 -> PrimIO SsizeT

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Creates a new endpoint for communication returning a file descriptor
||| referring to that endpoint.
export %inline
socket : (d : Domain) -> SockType -> EPrim (Socket d)
socket d (ST st) = toVal cast (prim__socket (domainCode d) st)

||| Listen for connections on a socket.
|||
||| This marks the socket as the *passive* part that will then wait
||| for incoming connections using calles to `accept`.
export %inline
listen : Socket d -> (backlog : Bits32) -> EPrim ()
listen s backlog = toUnit (prim__listen (fileDesc s) backlog)

||| Accept connections on a socket.
|||
||| Incoming connections are returned as new `Socket` file descriptors.
export %inline
accept : Socket d -> EPrim (Socket d)
accept s = toVal cast (prim__accept (fileDesc s))

||| Binds a socket to the given address. See also `bind` for a more
||| convenient version of this function.
export
bind_ : {d : _} -> Socket d -> Sockaddr d -> EPrim ()
bind_ s a = toUnit $ prim__bind (fileDesc s) (ptr d a) (addrSize d)

||| Connects a socket to the given address. See also `connect` for a more
||| convenient version of this function.
export
connect_ : {d : _} -> Socket d -> Sockaddr d -> EPrim ()
connect_ s a = toUnit $ prim__connect (fileDesc s) (ptr d a) (addrSize d)

parameters (s : Socket d)
  ||| Reads at most `n` bytes from a file into an allocated pointer.
  export %inline
  recvPtr : (0 r : Type) -> FromPtr r => CPtr -> SockFlags -> EPrim (ReadRes r)
  recvPtr r (CP sz p) (SF f) = ptrToRes p $ prim__recvptr (fileDesc s) p sz f

  ||| Reads at most `n` bytes from a file into a bytestring.
  export
  recv : (0 r : Type) -> FromBuf r => Bits32 -> SockFlags -> EPrim (ReadRes r)
  recv r n (SF f) = toRes n $ \b,x => prim__recv (fileDesc s) b x f

||| Reads at most `n` bytes from a file into an allocated pointer.
export %inline
recvFromPtr :
     {d : _}
  -> Socket d
  -> (0 r : Type)
  -> {auto frp : FromPtr r}
  -> CPtr
  -> SockFlags
  -> Sockaddr d
  -> EPrim r
recvFromPtr s r (CP sz pt) (SF f) p =
  ptrRead pt $ prim__recvfromptr (fileDesc s) pt sz f (ptr d p) (addrSize d)

||| Reads at most `n` bytes from a file into an allocated pointer.
export %inline
recvFrom :
     {d : _}
  -> Socket d
  -> (0 r : Type)
  -> {auto frb : FromBuf r}
  -> (n : Bits32)
  -> SockFlags
  -> Sockaddr d
  -> EPrim r
recvFrom s r n (SF f) p =
  allocRead n $ \buf,x => prim__recvfrom (fileDesc s) buf x f (ptr d p) (addrSize d)

||| Sends the given byte string via the given socket to the peer at the
||| given address.
export %inline
sendto :
     {d : _}
  -> {auto tob : ToBuf r}
  -> Socket d
  -> r
  -> SockFlags
  -> Sockaddr d
  -> EPrim Bits32
sendto s v (SF f) p =
  case unsafeToBuf v of
    Left (CP sz pt) =>
      toSize $ prim__sendtoptr (fileDesc s) pt 0 sz f (ptr d p) (addrSize d)
    Right (BS n $ BV b o _) =>
      toSize $ prim__sendto
        (fileDesc s)
        (unsafeGetBuffer b)
        (cast o)
        (cast n)
        f
        (ptr d p)
        (addrSize d)

--------------------------------------------------------------------------------
-- Convenience API
--------------------------------------------------------------------------------

||| Convenience alias for `bind_`.
export
bind : {d : _} -> Socket d -> Addr d -> EPrim ()
bind s a t =
  let addr # t := sockaddr d a t
   in finally (prim__free $ ptr d addr) (bind_ s addr) t

||| Convenience alias for `connect_`.
export
connect : {d : _} -> Socket d -> Addr d -> EPrim ()
connect s a t =
  let addr # t := sockaddr d a t
   in finally (prim__free $ ptr d addr) (connect_ s addr) t
