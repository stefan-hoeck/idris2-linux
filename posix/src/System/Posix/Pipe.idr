module System.Posix.Pipe

import public System.Posix.File

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_pipe, posix-idris"
prim__pipe : AnyPtr -> PrimIO CInt

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Creates a pipe and writes the two file descriptors into the given C-array,
||| the read end at position 0 the write end at position 1.
export %inline
pipe : CArrayIO 2 Fd -> IO (Either Errno ())
pipe p = toUnit $ prim__pipe (unsafeUnwrap p)
