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

%foreign "C:li_bind_un, posix-idris"
prim__bind_un : Bits32 -> String -> PrimIO CInt

%foreign "C:li_connect_un, posix-idris"
prim__connect_un : Bits32 -> String -> PrimIO CInt

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

||| Binds a socket to the given address.
export
bind : {d : _} -> Socket d -> String -> EPrim ()
bind {d = AF_UNIX}  s pth = toUnit $ prim__bind_un (fileDesc s) pth
bind {d = AF_INET}  s pth = ?bind_inet
bind {d = AF_INET6} s pth = ?bind_inet6

||| Connects a socket to the given address.
export
connect : {d : _} -> Socket d -> String -> EPrim ()
connect {d = AF_UNIX}  s pth = toUnit $ prim__connect_un (fileDesc s) pth
connect {d = AF_INET}  s pth = ?connect_inet
connect {d = AF_INET6} s pth = ?connect_inet6
