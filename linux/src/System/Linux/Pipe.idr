module System.Linux.Pipe

import System.Linux.Pipe.Prim as P
import public System.Posix.Pipe

%default total

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Linux-specific version of `pipe` that allows setting additional
||| flags (`O_NONBLOCK`, `O_CLOEXEC`, `O_DIRECT`).
export %inline
pipe2 : ErrIO io => CArrayIO 2 Fd -> Flags -> io ()
pipe2 p = eprim . P.pipe2 p
