module System.Posix.File.ReadRes

import Derive.Prelude

import public Data.Buffer
import public Data.Buffer.Core
import public System.Posix.Errno

%default total
%language ElabReflection

||| Result of a (potentially non-blocking) read, typically from a pipe
||| or socket.
public export
data ReadRes : Type -> Type where
  ||| The system call was interrupted by a signal.
  Interrupted : ReadRes a

  ||| There is currently no data avialable (this will only be a possible
  ||| outcome when reading in non-blocking mode).
  NoData      : ReadRes a

  ||| Tried to read from a closed connection or pipe.
  Closed      : ReadRes a

  ||| We reached the end of input.
  EOI         : ReadRes a

  ||| We got `n` bytes of data.
  Res         : (res : a) -> ReadRes a

%runElab derive "ReadRes" [Show,Eq]

export
Functor ReadRes where
  map f Interrupted = Interrupted
  map f NoData      = NoData
  map f Closed      = Closed
  map f EOI         = EOI
  map f (Res res)   = Res (f res)

export
Foldable ReadRes where
  foldr f v (Res r) = f r v
  foldr _ v _       = v

export
Traversable ReadRes where
  traverse f Interrupted = pure Interrupted
  traverse f NoData      = pure NoData
  traverse f Closed      = pure Closed
  traverse f EOI         = pure EOI
  traverse f (Res res)   = Res <$> f res

export
fromErr : Errno -> EPrim (ReadRes a)
fromErr err t =
  if      err == EAGAIN      then R NoData t
  else if err == EWOULDBLOCK then R NoData t
  else if err == EINTR       then R Interrupted t
  else if err == EPIPE       then R Closed t
  else                            E err t
