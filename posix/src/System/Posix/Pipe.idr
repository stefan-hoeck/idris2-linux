module System.Posix.Pipe

import System.Posix.Pipe.Prim as P

import public System.Posix.Errno
import public System.Posix.File

%default total

||| Creates a pipe and writes the two file descriptors into the given C-array,
||| the read end at position 0 the write end at position 1.
export %inline
pipe : ErrIO io => CArrayIO 2 Fd -> io ()
pipe = eprim . P.pipe

||| Creates a new FIFO (named pipe) on disc.
export %inline
mkfifo : ErrIO io => String -> ModeT -> io ()
mkfifo s = eprim . P.mkfifo s
