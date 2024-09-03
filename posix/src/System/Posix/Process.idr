module System.Posix.Process

import Data.C.Integer
import System.Posix.Errno
import System.Posix.File

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:getpid, posix-idris"
prim__getpid : PrimIO PidT

%foreign "C:getppid, posix-idris"
prim__getppid : PrimIO PidT

%foreign "C:getuid, posix-idris"
prim__getuid : PrimIO UidT

%foreign "C:geteuid, posix-idris"
prim__geteuid : PrimIO UidT

%foreign "C:getgid, posix-idris"
prim__getgid : PrimIO GidT

%foreign "C:getegid, posix-idris"
prim__getegid : PrimIO GidT

%foreign "C:li_setuid, posix-idris"
prim__setuid : UidT -> PrimIO CInt

%foreign "C:li_seteuid, posix-idris"
prim__seteuid : UidT -> PrimIO CInt

%foreign "C:li_setgid, posix-idris"
prim__setgid : GidT -> PrimIO CInt

%foreign "C:li_setegid, posix-idris"
prim__setegid : GidT -> PrimIO CInt

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Returns the process ID of the current process
export %inline
getpid : HasIO io => io PidT
getpid = primIO prim__getpid

||| Returns the process ID of the current process' parent process
export %inline
getppid : HasIO io => io PidT
getppid = primIO prim__getppid

||| Returns the real user ID of the current process
export %inline
getuid : HasIO io => io UidT
getuid = primIO prim__getuid

||| Returns the effective user ID of the current process
export %inline
geteuid : HasIO io => io UidT
geteuid = primIO prim__geteuid

||| Returns the real group ID of the current process
export %inline
getgid : HasIO io => io GidT
getgid = primIO prim__getgid

||| Returns the effective group ID of the current process
export %inline
getegid : HasIO io => io GidT
getegid = primIO prim__getegid

||| Tries to set the real user ID of the current process
export %inline
setuid : UidT -> IO (Either Errno ())
setuid uid = toUnit $ prim__setuid uid

||| Tries to set the effective user ID of the current process
export %inline
seteuid : UidT -> IO (Either Errno ())
seteuid uid = toUnit $ prim__seteuid uid

||| Tries to set the real group ID of the current process
export %inline
setgid : GidT -> IO (Either Errno ())
setgid gid = toUnit $ prim__setgid gid

||| Tries to set the effective group ID of the current process
export %inline
setegid : GidT -> IO (Either Errno ())
setegid gid = toUnit $ prim__setegid gid
