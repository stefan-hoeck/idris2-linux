module System.Linux.Epoll.Struct

import Data.C.Ptr
import Derive.Prelude

import System.Linux.Epoll.Flags
import System.Posix.File.FileDesc

%default total
%language ElabReflection

%foreign "C:get_epoll_event_events, linux-idris"
prim__get_epoll_event_events : AnyPtr -> PrimIO Bits32

%foreign "C:get_epoll_event_fd, linux-idris"
prim__get_epoll_event_fd : AnyPtr -> PrimIO Bits32

||| A file descriptor used for monitoring other file descriptors in
||| calls to `epoll_ctl` and `epoll_wait`.
export
record Epollfd where
  constructor EFD
  fd : Bits32

export %inline
Cast Epollfd Fd where cast = MkFd . fd

export %inline
Cast CInt Epollfd where cast = EFD . cast

||| Wrapper around a pointer of an `epoll_event` value.
export
record SEpollEvent where
  constructor SE
  ptr : AnyPtr

export %inline
Struct SEpollEvent where
  wrap   = SE
  unwrap = ptr

export %inline
SizeOf SEpollEvent where sizeof_ = epoll_event_size

||| Wrapper around a pointer of an `epoll_event` value.
public export
record EpollEvent where
  constructor E
  event : Event
  file  : Fd

%runElab derive "EpollEvent" [Show,Eq]

export
epollEvent : SEpollEvent -> PrimIO EpollEvent
epollEvent (SE p) w =
  let MkIORes fd w := prim__get_epoll_event_fd p w
      MkIORes ev w := prim__get_epoll_event_events p w
   in MkIORes (E (E ev) (cast fd)) w
