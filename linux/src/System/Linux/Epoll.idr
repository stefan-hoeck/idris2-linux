module System.Linux.Epoll

import System.Linux.Epoll.Prim as P

import System.Posix.Signal
import System.Posix.Timer

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

export %inline
epollPwait2 :
     {n : _}
  -> {auto eio : ErrIO io}
  -> Epollfd
  -> CArrayIO n SEpollEvent
  -> Clock Duration
  -> List Signal
  -> io (k ** CArrayIO k SEpollEvent)
epollPwait2 efd arr timeout = eprim . P.epollPwait2 efd arr timeout

export %inline
epollPwait2Vals :
     {n : _}
  -> {auto eio : ErrIO io}
  -> Epollfd
  -> CArrayIO n SEpollEvent
  -> Clock Duration
  -> List Signal
  -> io (List EpollEvent)
epollPwait2Vals efd arr timeout = eprim . P.epollPwait2Vals efd arr timeout
