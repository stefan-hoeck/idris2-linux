module System.Posix.Socket.Prim

import public Data.C.Ptr
import public System.Posix.Errno
import public System.Posix.Socket.Struct
import public System.Posix.Socket.Types

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_socket, posix-idris"
prim__socket : Bits8 -> Bits32 -> PrimIO CInt

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Creates a new endpoint for communication returning a file descriptor
||| referring to that endpoint.
export %inline
socket : Domain -> SockType -> EPrim Socket
socket d (ST st) = toVal cast (prim__socket (domainCode d) st)
