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
