module System.Posix.Pipe

import System.Posix.Pipe.Prim as P

import public System.Posix.Errno
import public System.Posix.File

%default total

||| Creates a pipe and writes the two file descriptors into the given C-array,
||| the read end at position 0 the write end at position 1.
export %inline
pipe : Has Errno es => EIO1 f => CArrayIO 2 Fd -> f es ()
pipe arr = elift1 (P.pipe arr)

||| Creates a new FIFO (named pipe) on disc.
export %inline
mkfifo : Has Errno es => EIO1 f => String -> ModeT -> f es ()
mkfifo s m = elift1 (P.mkfifo s m)
