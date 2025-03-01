module System.Posix.Poll.Struct

import Data.C.Ptr
import System.Posix.File.FileDesc
import System.Posix.Poll.Types

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:get_pollfd_fd, posix-idris"
prim__get_pollfd_fd: AnyPtr -> PrimIO Bits32

%foreign "C:set_pollfd_fd, posix-idris"
prim__set_pollfd_fd: AnyPtr -> Bits32 -> PrimIO ()

%foreign "C:get_pollfd_events, posix-idris"
prim__get_pollfd_events: AnyPtr -> PrimIO Bits32

%foreign "C:set_pollfd_events, posix-idris"
prim__set_pollfd_events: AnyPtr -> Bits32 -> PrimIO ()

%foreign "C:get_pollfd_revents, posix-idris"
prim__get_pollfd_revents: AnyPtr -> PrimIO Bits32

%foreign "C:set_pollfd_revents, posix-idris"
prim__set_pollfd_revents: AnyPtr -> Bits32 -> PrimIO ()

--------------------------------------------------------------------------------
-- SPollFD
--------------------------------------------------------------------------------

||| A wrapper around a `struct pollfd` pointer.
export
record SPollFD (s : Type) where
  constructor PF
  ptr : AnyPtr

export %inline
Struct SPollFD where
  swrap   = PF
  sunwrap = ptr

public export %inline
SizeOf (SPollFD s) where
  sizeof_ = pollfd_size

public export
0 PollFD : Type
PollFD = SPollFD World

||| Reads the `fd` field of a `struct pollfd` pointer.
export %inline
pollfd : SPollFD s -> F1 s Fd
pollfd (PF p) t =
  let v # t := ffi (prim__get_pollfd_fd p) t
   in MkFd v # t

||| Sets the `fd` field of a `struct pollfd` pointer.
export %inline
setPollfd : SPollFD s -> Fd -> F1' s
setPollfd (PF p) (MkFd v) = ffi (prim__set_pollfd_fd p v)

||| Reads the `events` field of a `struct pollfd` pointer.
export %inline
events : SPollFD s -> F1 s PollEvent
events (PF p) t =
  let v # t := ffi (prim__get_pollfd_events p) t
   in PE v # t

||| Sets the `events` field of a `struct pollfd` pointer.
export %inline
setEvents : SPollFD s -> PollEvent -> F1' s
setEvents (PF p) (PE v) = ffi (prim__set_pollfd_events p v)

||| Reads the `revents` field of a `struct pollfd` pointer.
export %inline
revents : SPollFD s -> F1 s PollEvent
revents (PF p) t =
  let v # t := ffi (prim__get_pollfd_revents p) t
   in PE v # t

||| Sets the `revents` field of a `struct pollfd` pointer.
export %inline
setRevents : SPollFD s -> PollEvent -> F1' s
setRevents (PF p) (PE v) = ffi (prim__set_pollfd_revents p v)

--------------------------------------------------------------------------------
-- PollPair
--------------------------------------------------------------------------------

public export
record PollPair where
  constructor PP
  fd     : Fd
  events : PollEvent

export
pollResults : {n : _} -> CArray s n (SPollFD s) -> F1 s (List PollPair)
pollResults arr = go [] n
  where
    go : List PollPair -> (m : Nat) -> (0 p : LTE m n) => F1 s (List PollPair)
    go xs 0     t = xs # t
    go xs (S k) t =
      let spfd # t := getStructNat arr k t
          fd   # t := pollfd spfd t
          evs  # t := revents spfd t
       in if evs == 0 then go xs k t else go (PP fd evs :: xs) k t

export
writeFiles : {n : _} -> CArray s n (SPollFD s) -> List PollPair -> F1' s
writeFiles arr = go n
  where
    go : (m : Nat) -> (ix : Ix m n) => List PollPair -> F1' s
    go (S k) (x::xs) t =
      let spfd # t := getStructIx arr k t
          _    # t := setPollfd spfd x.fd t
          _    # t := setEvents spfd x.events t
       in go k xs t
    go _     _       t = () # t
