module System.Linux.Pipe

import public System.Posix.Pipe

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_pipe2, linux-idris"
prim__pipe2 : AnyPtr -> Bits32 -> PrimIO CInt

%foreign "C:li_o_direct, linux-idris"
o_direct : Bits32

||| With this flag set, a pipe will treat every `write` as a distinct data
||| package, and `read` will read one package at a time.
|||
||| Note, that when writing more than `PIPE_BUF` bytes at a time, the data
||| will be split into smaller packages.
export %inline
O_DIRECT : Flags
O_DIRECT = F o_direct

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Linux-specific version of `pipe` that allows setting additional
||| flags (`O_NONBLOCK`, `O_CLOEXEC`, `O_DIRECT`).
export %inline
pipe2 : ErrIO io => CArrayIO 2 Fd -> Flags -> io ()
pipe2 p (F fs) = toUnit $ prim__pipe2 (unsafeUnwrap p) fs
