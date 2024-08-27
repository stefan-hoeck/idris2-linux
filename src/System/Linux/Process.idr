module System.Linux.Process

import Data.C.Integer


%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:getpid, linux-idris"
prim__getpid : PrimIO PidT

%foreign "C:getppid, linux-idris"
prim__getppid : PrimIO PidT

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
