module System.Posix.Socket

import System.Posix.Socket.Prim as P

import public System.Posix.Socket.Struct
import public System.Posix.Socket.Types
import public System.Posix.File.ReadRes

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
  bind_ : {d : _} -> Socket d -> Sockaddr d -> io ()
  bind_ s = eprim . P.bind_ s

  ||| Connects a socket to the given address.
  export %inline
  connect_ : {d : _} -> Socket d -> Sockaddr d -> io ()
  connect_ s = eprim . P.connect_ s

  ||| Convenience alias for `bind_`.
  export
  bind : {d : _} -> Socket d -> Addr d -> io ()
  bind s = eprim . P.bind s

  ||| Convenience alias for `connect_`.
  export
  connect : {d : _} -> Socket d -> Addr d -> io ()
  connect s = eprim . P.connect s

  ||| Reads at most `n` bytes from a file into an allocated pointer.
  export %inline
  recvPtr :
       Socket d
    -> (0 r : Type)
    -> {auto frp : FromPtr r}
    -> CPtr
    -> SockFlags
    -> io (ReadRes r)
  recvPtr s r cp = eprim . P.recvPtr s r cp

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
    -> io r
  recvFromPtr s r cp sf = eprim . P.recvFromPtr s r cp sf

  ||| Reads at most `n` bytes from a file into a bytestring.
  export %inline
  recv :
       Socket d
    -> (0 r : Type)
    -> {auto frb : FromBuf r}
    -> (n : Bits32)
    -> SockFlags
    -> io (ReadRes r)
  recv s r n = eprim . P.recv s r n

  ||| Reads at most `n` bytes from a socket into a bytestring
  export %inline
  recvFrom :
      {d : _}
    -> Socket d
    -> (0 r : Type)
    -> {auto frb : FromBuf r}
    -> (n : Bits32)
    -> SockFlags
    -> Sockaddr d
    -> io r
  recvFrom s r n sf = eprim . P.recvFrom s r n sf

  export
  sendto :
       {d : _}
    -> {auto tob : ToBuf r}
    -> Socket d
    -> r
    -> SockFlags
    -> Sockaddr d
    -> io Bits32
  sendto s r f = eprim . P.sendto s r f
