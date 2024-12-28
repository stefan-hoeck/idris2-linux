module System.Posix.Pipe.Prim

import public System.Posix.File.Prim

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_pipe, posix-idris"
prim__pipe : AnyPtr -> PrimIO CInt

%foreign "C:li_mkfifo, posix-idris"
prim__mkfifo : String -> ModeT -> PrimIO CInt

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Creates a pipe and writes the two file descriptors into the given C-array,
||| the read end at position 0 the write end at position 1.
export %inline
pipe : CArrayIO 2 Fd -> EPrim ()
pipe p = toUnit $ prim__pipe (unsafeUnwrap p)

||| Creates a new FIFO (named pipe) on disc.
export %inline
mkfifo : String -> ModeT -> EPrim ()
mkfifo pth m = toUnit $ prim__mkfifo pth m
