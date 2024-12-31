module System.Linux.Pipe.Prim

import System.Posix.Pipe.Prim

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_pipe2, linux-idris"
prim__pipe2 : AnyPtr -> Bits32 -> PrimIO CInt

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Linux-specific version of `pipe` that allows setting additional
||| flags (`O_NONBLOCK`, `O_CLOEXEC`, `O_DIRECT`).
export %inline
pipe2 : CArrayIO 2 Fd -> Flags -> EPrim ()
pipe2 p (F fs) = toUnit $ prim__pipe2 (unsafeUnwrap p) fs
