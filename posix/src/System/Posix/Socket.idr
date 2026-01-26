module System.Posix.Socket

import System.Posix.Socket.Prim as P

import public System.Posix.Socket.Struct
import public System.Posix.Socket.Types
import public System.Posix.File.ReadRes

parameters {auto has : Has Errno es}
           {auto eio : EIO1 f}

  ||| Creates a new endpoint for communication returning a file descriptor
  ||| referring to that endpoint.
  export %inline
  socket : (d : Domain) -> SockType -> f es (Socket d)
  socket d t = elift1 $ P.socket d t

  ||| Listen for connections on a socket.
  |||
  ||| This marks the socket as the *passive* part that will then wait
  ||| for incoming connections using calles to `accept`.
  export %inline
  listen : Socket d -> (backlog : Bits32) -> f es ()
  listen s b = elift1 $ P.listen s b

  ||| Accept connections on a socket.
  |||
  ||| Incoming connections are returned as new `Socket` file descriptors.
  export %inline
  accept : Socket d -> f es (Socket d)
  accept s = elift1 $ P.accept s

  ||| Binds a socket to the given address.
  export %inline
  bind_ : {d : _} -> Socket d -> Sockaddr d -> f es ()
  bind_ s a = elift1 $ P.bind_ s a

  ||| Connects a socket to the given address.
  export %inline
  connect_ : {d : _} -> Socket d -> Sockaddr d -> f es ()
  connect_ s a = elift1 $ P.connect_ s a

  ||| Convenience alias for `bind_`.
  export
  bind : {d : _} -> Socket d -> Addr d -> f es ()
  bind s a = elift1 $ P.bind s a

  ||| Convenience alias for `connect_`.
  export
  connect : {d : _} -> Socket d -> Addr d -> f es ()
  connect s a = elift1 $ P.connect s a

  ||| Reads at most `n` bytes from a file into an allocated pointer.
  export %inline
  recvPtr :
       Socket d
    -> (0 r : Type)
    -> {auto frp : FromPtr r}
    -> CPtr
    -> SockFlags
    -> f es (ReadRes r)
  recvPtr s r cp fs = elift1 $ P.recvPtr s r cp fs

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
    -> f es r
  recvFromPtr s r cp sf a = elift1 $ P.recvFromPtr s r cp sf a

  ||| Reads at most `n` bytes from a file into a bytestring.
  export %inline
  recv :
       Socket d
    -> (0 r : Type)
    -> {auto frb : FromBuf r}
    -> (n : Bits32)
    -> SockFlags
    -> f es (ReadRes r)
  recv s r n fs = elift1 $ P.recv s r n fs

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
    -> f es r
  recvFrom s r n sf a = elift1 $ P.recvFrom s r n sf a

  export
  sendto :
       {d : _}
    -> {auto tob : ToBuf r}
    -> Socket d
    -> r
    -> SockFlags
    -> Sockaddr d
    -> f es Bits32
  sendto s r f a = elift1 $ P.sendto s r f a

  ||| Returns the address of the peer connected to a socket.
  ||| The given Sockaddr buffer will be filled with the peer address.
  export %inline
  getpeername_ : {d : _} -> Socket d -> Sockaddr d -> f es ()
  getpeername_ s a = elift1 $ P.getpeername_ s a

  ||| Returns the current address to which the socket is bound.
  ||| The given Sockaddr buffer will be filled with the socket's address.
  export %inline
  getsockname_ : {d : _} -> Socket d -> Sockaddr d -> f es ()
  getsockname_ s a = elift1 $ P.getsockname_ s a

  ||| Returns the address of the peer connected to a socket.
  export %inline
  getpeername : {d : _} -> Socket d -> f es (Addr d)
  getpeername s = elift1 $ P.getpeername s

  export %inline
  getsockname : {d : _} -> Socket d -> f es (Addr d)
  getsockname s = elift1 $ P.getsockname s

  ||| Enables or disables the Nagle algorithm.
  export %inline
  setNoDelay : Socket d -> Bool -> f es ()
  setNoDelay s b = elift1 $ P.setNoDelay s b

  ||| Allows binding to an address/port before the expiry of the TIME_WAIT state.
  export %inline
  setReuseAddress : Socket d -> Bool -> f es ()
  setReuseAddress s b = elift1 $ P.setReuseAddress s b

  ||| Sets the linger option for a socket.
  |||
  ||| `Nothing` disables lingering (close returns immediately).
  ||| `Just 0` enables a hard close (RST sent, data discarded).
  ||| `Just n` for n > 0 waits up to n seconds for data to be sent before closing.
  export %inline
  setLinger : Socket d -> Maybe Bits32 -> f es ()
  setLinger s t = elift1 $ P.setLinger s t
