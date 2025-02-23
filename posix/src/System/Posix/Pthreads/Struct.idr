module System.Posix.Pthreads.Struct

import public Data.C.Ptr
import public System.Posix.Errno
import public System.Posix.Pthreads.Types

%default total

--------------------------------------------------------------------------------
-- PthreadT
--------------------------------------------------------------------------------

%foreign "C:pthread_equal, posix-idris"
prim__pthread_equal : AnyPtr -> AnyPtr -> Bits8

||| Wrapper around an identifier for a POSIX thread.
public export
record PthreadT where
  constructor P
  ptr : AnyPtr

export %inline
Eq PthreadT where
  x == y = toBool (prim__pthread_equal x.ptr y.ptr)

||| Warning: This `Show` implementation for thread IDs is for debugging only!
||| According to SUSv3, a thread ID need not be a scalar, so it should be
||| treated as an opaque type.
|||
||| On many implementations (including on Linux), they are just integers, so
||| this can be useful for debugging.
export %inline
Show PthreadT where
  show (P p) = show (believe_me {b = Bits64} p)

||| Wrapper around a `pthread_mutex_t` pointer.
|||
||| Noted: While this provides additional flexibility over the type of mutex
||| we use (see `mkmutex`) and how we acquire a lock on a mutex, it is less
||| convenient to use than the garbage-collected version from
||| `System.Concurrency`.
public export
record SMutexT (s : Type) where
  constructor M
  ptr : AnyPtr

public export
0 MutexT : Type
MutexT = SMutexT World

||| Wrapper around a `pthread_cond_t` pointer.
|||
||| Noted: While this provides additional flexibility over the type of condition
||| we use (see `mkcond`) convenient to use than the garbage-collected version from
||| `System.Concurrency`.
public export
record SCondT (s : Type) where
  constructor C
  ptr : AnyPtr

public export
0 CondT : Type
CondT = SCondT World
