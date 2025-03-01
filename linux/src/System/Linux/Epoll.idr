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
epollCreate : Has Errno es => EIO1 f => EpollFlags -> f es Epollfd
epollCreate fs = elift1 (P.epollCreate fs)

export %inline
epollCtl :
     {auto ifd : FileDesc g}
  -> {auto has : Has Errno es}
  -> {auto eio : EIO1 f}
  -> Epollfd
  -> EpollOp
  -> (fd : g)
  -> PollEvent
  -> f es ()
epollCtl efd op fd ev = elift1 (P.epollCtl efd op fd ev)

export %inline
epollWait :
     {n : _}
  -> {auto has : Has Errno es}
  -> {auto eio : EIO1 f}
  -> Epollfd
  -> CArrayIO n SEpollEvent
  -> Int32
  -> f es (k ** CArrayIO k SEpollEvent)
epollWait efd arr timeout = elift1 (P.epollWait efd arr timeout)

export %inline
epollWaitVals :
     {n : _}
  -> {auto has : Has Errno es}
  -> {auto eio : EIO1 f}
  -> Epollfd
  -> CArrayIO n SEpollEvent
  -> Int32
  -> f es (List PollPair)
epollWaitVals efd arr timeout = elift1 (P.epollWaitVals efd arr timeout)

export %inline
epollPwait2 :
     {n : _}
  -> {auto has : Has Errno es}
  -> {auto eio : EIO1 f}
  -> Epollfd
  -> CArrayIO n SEpollEvent
  -> Clock Duration
  -> List Signal
  -> f es (k ** CArrayIO k SEpollEvent)
epollPwait2 efd arr timeout ss = elift1 (P.epollPwait2 efd arr timeout ss)

export %inline
epollPwait2Vals :
     {n : _}
  -> {auto has : Has Errno es}
  -> {auto eio : EIO1 f}
  -> Epollfd
  -> CArrayIO n SEpollEvent
  -> Clock Duration
  -> List Signal
  -> f es (List PollPair)
epollPwait2Vals efd arr timeout ss = elift1 (P.epollPwait2Vals efd arr timeout ss)
