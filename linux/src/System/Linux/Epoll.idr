module System.Linux.Epoll

import System.Linux.Epoll.Prim as P

import public Data.C.Ptr
import public System.Linux.Epoll.Flags
import public System.Linux.Epoll.Struct
import public System.Posix.File

%default total

||| Opens a new `epoll` file descriptor.
export %inline
epollCreate : ErrIO io => EpollFlags -> io Epollfd
epollCreate = eprim . P.epollCreate

export %inline
epollCtl :
     {auto ifd : FileDesc f}
  -> {auto eio : ErrIO io}
  -> Epollfd
  -> EpollOp
  -> (fd : f)
  -> Event
  -> io ()
epollCtl efd op fd = eprim . P.epollCtl efd op fd

export %inline
epollWait :
     {n : _}
  -> {auto eio : ErrIO io}
  -> Epollfd
  -> CArrayIO n SEpollEvent
  -> Int32
  -> io (k ** CArrayIO k SEpollEvent)
epollWait efd arr = eprim . P.epollWait efd arr

export %inline
epollWaitVals :
     {n : _}
  -> {auto eio : ErrIO io}
  -> Epollfd
  -> CArrayIO n SEpollEvent
  -> Int32
  -> io (List EpollEvent)
epollWaitVals efd arr = eprim . P.epollWaitVals efd arr
