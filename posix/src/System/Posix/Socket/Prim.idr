module System.Posix.Socket.Prim

import public Data.C.Ptr
import public System.Posix.Errno
import public System.Posix.File.FileDesc
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
