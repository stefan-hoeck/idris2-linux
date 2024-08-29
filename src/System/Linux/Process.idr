module System.Linux.Process

import Data.C.Integer
import System.Linux.Error

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:getpid, linux-idris"
prim__getpid : PrimIO PidT

%foreign "C:getppid, linux-idris"
prim__getppid : PrimIO PidT

%foreign "C:getuid, linux-idris"
prim__getuid : PrimIO UidT

%foreign "C:geteuid, linux-idris"
prim__geteuid : PrimIO UidT

%foreign "C:getgid, linux-idris"
prim__getgid : PrimIO GidT

%foreign "C:getegid, linux-idris"
prim__getegid : PrimIO GidT

%foreign "C:li_setuid, linux-idris"
prim__setuid : UidT -> PrimIO CInt

%foreign "C:li_seteuid, linux-idris"
prim__seteuid : UidT -> PrimIO CInt

%foreign "C:li_setgid, linux-idris"
prim__setgid : GidT -> PrimIO CInt

%foreign "C:li_setegid, linux-idris"
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
setuid : UidT -> IO (Either Error ())
setuid uid = toUnit id $ prim__setuid uid

||| Tries to set the effective user ID of the current process
export %inline
seteuid : UidT -> IO (Either Error ())
seteuid uid = toUnit id $ prim__seteuid uid

||| Tries to set the real group ID of the current process
export %inline
setgid : GidT -> IO (Either Error ())
setgid gid = toUnit id $ prim__setgid gid

||| Tries to set the effective group ID of the current process
export %inline
setegid : GidT -> IO (Either Error ())
setegid gid = toUnit id $ prim__setegid gid
