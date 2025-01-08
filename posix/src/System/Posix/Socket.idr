module System.Posix.Socket

import System.Posix.Socket.Prim as P

import public System.Posix.Socket.Struct
import public System.Posix.Socket.Types

parameters {auto eio : ErrIO io}

  ||| Creates a new endpoint for communication returning a file descriptor
  ||| referring to that endpoint.
  export %inline
  socket : (d : Domain) -> SockType -> io (Socket d)
  socket d = eprim . P.socket d

  ||| Listen for connections on a socket.
  |||
  ||| This marks the socket as the *passive* part that will then wait
  ||| for incoming connections using calles to `accept`.
  export %inline
  listen : Socket d -> (backlog : Bits32) -> io ()
  listen s = eprim . P.listen s

  ||| Accept connections on a socket.
  |||
  ||| Incoming connections are returned as new `Socket` file descriptors.
  export %inline
  accept : Socket d -> io (Socket d)
  accept = eprim . P.accept

  ||| Binds a socket to the given address.
  export %inline
  bind : {d : _} -> Socket d -> String -> io ()
  bind s = eprim . P.bind s

  ||| Connects a socket to the given address.
  export %inline
  connect : {d : _} -> Socket d -> String -> io ()
  connect s = eprim . P.connect s
