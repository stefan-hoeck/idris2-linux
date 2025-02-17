module System.Linux.Epoll.Prim

import Data.C.Ptr
import Data.C.Array

import System.Posix.Signal.Prim
import System.Posix.Timer.Prim

import public System.Linux.Epoll.Flags
import public System.Linux.Epoll.Struct
import public System.Posix.File.Prim

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_epoll_create, linux-idris"
prim__epoll_create : Bits32 -> PrimIO CInt

%foreign "C:li_epoll_ctl, linux-idris"
prim__epoll_ctl : Bits32 -> Bits32 -> Bits32 -> Bits32 -> PrimIO CInt

%foreign "C__collect_safe:li_epoll_wait, linux-idris"
prim__epoll_wait : Bits32 -> AnyPtr -> Bits32 -> Int32 -> PrimIO CInt

%foreign "C__collect_safe:li_epoll_pwait2, linux-idris"
prim__epoll_pwait2 : Bits32 -> AnyPtr -> Bits32 -> AnyPtr -> PrimIO CInt

%foreign "C__collect_safe:li_epoll_spwait2, linux-idris"
prim__epoll_spwait2 : Bits32 -> AnyPtr -> Bits32 -> AnyPtr -> AnyPtr -> PrimIO CInt

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Opens a new `epoll` file descriptor.
export %inline
epollCreate : EpollFlags -> EPrim Epollfd
epollCreate (F f) = toVal cast $ prim__epoll_create f

export %inline
epollCtl :
     {auto ifd : FileDesc f}
  -> Epollfd
  -> EpollOp
  -> (fd : f)
  -> Event
  -> EPrim ()
epollCtl efd op fd (E ev) =
  toUnit $ prim__epoll_ctl (fileDesc efd) (opCode op) (fileDesc fd) ev

export
epollWait :
     {n : _}
  -> Epollfd
  -> CArrayIO n SEpollEvent
  -> Int32
  -> EPrim (k ** CArrayIO k SEpollEvent)
epollWait efd arr timeout t =
  let p     := unsafeUnwrap arr
      r # t := ffi (prim__epoll_wait (fileDesc efd) p (cast n) timeout) t
   in if r < 0 then E (inject $ fromNeg r) t else R (cast r ** unsafeWrap p) t

export
epollWaitVals :
     {n : _}
  -> Epollfd
  -> CArrayIO n SEpollEvent
  -> Int32
  -> EPrim (List EpollEvent)
epollWaitVals efd arr timeout t =
  let R (k ** arr2) t := epollWait efd arr timeout t | E x t => E x t
      vs # t          := values [] arr2 epollEvent k t
   in R vs t

export
epollPwait2 :
     {n : _}
  -> Epollfd
  -> CArrayIO n SEpollEvent
  -> Clock Duration
  -> List Signal
  -> EPrim (k ** CArrayIO k SEpollEvent)
epollPwait2 efd arr timeout [] =
  withTimespec timeout $ \ts,t =>
    let p     := unsafeUnwrap arr
        r # t := ffi (prim__epoll_pwait2 (fileDesc efd) p (cast n) (unwrap ts)) t
     in if r < 0 then E (inject $ fromNeg r) t else R (cast r ** unsafeWrap p) t
epollPwait2 efd arr timeout sigs =
  withTimespec timeout $ \ts => withSignals sigs $ \ss,t =>
    let p     := unsafeUnwrap arr
        r # t := ffi (prim__epoll_spwait2 (fileDesc efd) p (cast n) (unwrap ts) (unwrap ss)) t
     in if r < 0 then E (inject $ fromNeg r) t else R (cast r ** unsafeWrap p) t

export
epollPwait2Vals :
     {n : _}
  -> Epollfd
  -> CArrayIO n SEpollEvent
  -> Clock Duration
  -> List Signal
  -> EPrim (List EpollEvent)
epollPwait2Vals efd arr timeout sigs t =
  let R (k ** arr2) t := epollPwait2 efd arr timeout sigs t | E x t => E x t
      vs # t          := values [] arr2 epollEvent k t
   in R vs t
