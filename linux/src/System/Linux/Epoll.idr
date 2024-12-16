module System.Linux.Epoll

import public Data.C.Ptr
import public System.Linux.Epoll.Flags
import public System.Posix.File

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_epoll_create, linux-idris"
prim__epoll_create : Bits32 -> PrimIO CInt

%foreign "C:li_epoll_ctl, linux-idris"
prim__epoll_ctl : Bits32 -> Bits32 -> Bits32 -> Bits32 -> PrimIO CInt

%foreign "C:li_epoll_wait, linux-idris"
prim__epoll_wait : Bits32 -> AnyPtr -> Bits32 -> Int32 -> PrimIO CInt

%foreign "C:get_epoll_event_events, linux-idris"
prim__get_epoll_event_events : AnyPtr -> PrimIO Bits32

%foreign "C:get_epoll_event_fd, linux-idris"
prim__get_epoll_event_fd : AnyPtr -> PrimIO Bits32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| A file descriptor used for monitoring other file descriptors in
||| calls to `epoll_ctl` and `epoll_wait`.
export
record Epollfd where
  constructor EFD
  fd : Bits32

export %inline
Cast Epollfd Fd where cast = MkFd . fd

||| Opens a new `epoll` file descriptor.
export %inline
epollCreate : ErrIO io => EpollFlags -> io Epollfd
epollCreate (F f) = toVal (EFD . cast) $ prim__epoll_create f

export %inline
epollCtl :
     {auto eoi : ErrIO io}
  -> {auto ifd : FileDesc f}
  -> Epollfd
  -> EpollOp
  -> (fd : f)
  -> Event
  -> io ()
epollCtl (EFD efd) op fd (E ev) =
  toUnit $ prim__epoll_ctl efd (opCode op) (fileDesc fd) ev

||| Wrapper around a pointer of an `epoll_event` value.
export
record EpollEvent where
  constructor E
  ptr : AnyPtr

export %inline
Struct EpollEvent where
  wrap   = E
  unwrap = ptr

export %inline
SizeOf EpollEvent where sizeof_ = epoll_event_size

export %inline
epollWait :
     {auto eoi : ErrIO io}
  -> {n : _}
  -> Epollfd
  -> CArrayIO n EpollEvent
  -> Int32
  -> io (k ** CArrayIO k EpollEvent)
epollWait (EFD efd) arr timeout =
  let p := unsafeUnwrap arr
   in do
     num <- toVal cast $ prim__epoll_wait efd p (cast n) timeout
     pure (num ** unsafeWrap p)

export %inline
events : HasIO io => EpollEvent -> io Event
events (E p) =
  primIO $ \w =>
    let MkIORes n w := prim__get_epoll_event_events p w
     in MkIORes (E n) w

export %inline
fd : HasIO io => EpollEvent -> io Bits32
fd (E p) = primIO $ prim__get_epoll_event_fd p
