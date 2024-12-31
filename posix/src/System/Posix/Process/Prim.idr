module System.Posix.Process.Prim

import System.Posix.File
import System.Posix.Signal
import public Data.C.Ptr
import public System.Posix.Errno
import public System.Posix.Process.Flags
import public System.Posix.Process.ProcStatus

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

export %foreign "C:getpid, posix-idris"
getpid : PrimIO PidT

export %foreign "C:getppid, posix-idris"
getppid : PrimIO PidT

export %foreign "C:getuid, posix-idris"
getuid : PrimIO UidT

export %foreign "C:geteuid, posix-idris"
geteuid : PrimIO UidT

export %foreign "C:getgid, posix-idris"
getgid : PrimIO GidT

export %foreign "C:getegid, posix-idris"
getegid : PrimIO GidT

%foreign "C:li_setuid, posix-idris"
prim__setuid : UidT -> PrimIO CInt

%foreign "C:li_seteuid, posix-idris"
prim__seteuid : UidT -> PrimIO CInt

%foreign "C:li_setgid, posix-idris"
prim__setgid : GidT -> PrimIO CInt

%foreign "C:li_setegid, posix-idris"
prim__setegid : GidT -> PrimIO CInt

%foreign "C:li_fork, posix-idris"
prim__fork : PrimIO PidT

%foreign "C:li_wait, posix-idris"
prim__wait : AnyPtr -> PrimIO PidT

%foreign "C:li_waitpid, posix-idris"
prim__waitpid : PidT -> AnyPtr -> Bits32 -> PrimIO PidT

%foreign "C:li_waitid, posix-idris"
prim__waitid : Bits8 -> PidT -> AnyPtr -> Bits32 -> PrimIO PidT

%foreign "C:li_execve, posix-idris"
prim__execve : String -> AnyPtr -> AnyPtr -> PrimIO CInt

%foreign "C:li_execvp, posix-idris"
prim__execvp : String -> AnyPtr -> PrimIO CInt

%foreign "C:li_execv, posix-idris"
prim__execv : String -> AnyPtr -> PrimIO CInt

%foreign "C:li_system, posix-idris"
prim__system : String -> PrimIO CInt

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Tries to set the real user ID of the current process
export %inline
setuid : UidT -> EPrim ()
setuid uid = toUnit $ prim__setuid uid

||| Tries to set the effective user ID of the current process
export %inline
seteuid : UidT -> EPrim ()
seteuid uid = toUnit $ prim__seteuid uid

||| Tries to set the real group ID of the current process
export %inline
setgid : GidT -> EPrim ()
setgid gid = toUnit $ prim__setgid gid

||| Tries to set the effective group ID of the current process
export %inline
setegid : GidT -> EPrim ()
setegid gid = toUnit $ prim__setegid gid

||| Creates a new child process.
|||
||| This creates a new process by copying the stack, head, and
||| data memory segment of the parent process. If successful,
||| the functions returns `0` for the child process and
||| the child's process ID for the parent.
export %inline
fork : EPrim PidT
fork = toPidT Process.Prim.prim__fork

||| Loads a new program into this process's memory.
|||
||| `path` : The path of the program to run
||| `args` : Command-line arguments (a `NULL` terminated array of strings)
||| `env ` : Environment (a `NULL` terminated array of strings of the for "a=b")
|||
||| This only returns in case of an error.
export %inline
execve :
     String
  -> (args : CArrayIO m (Maybe String))
  -> (env  : CArrayIO n (Maybe String))
  -> EPrim ()
execve s a e = toUnit $ prim__execve s (unsafeUnwrap a) (unsafeUnwrap e)

||| Convenience alias of `execve` that uses Idris lists for passing
||| the arguments list and environment.
export
execle : String -> List String -> List (String,String) -> EPrim ()
execle s a e w =
  let MkIORes args w := toPrim (fromListIO (map Just a ++ [Nothing])) w
      MkIORes env  w := toPrim (fromListIO (map envpair e ++ [Nothing])) w
      R res w        := execve s args env w | E x w => E x w
      MkIORes _    w := toPrim (free args) w
      MkIORes _    w := toPrim (free env) w
   in R res w

  where
    envpair : (String,String) -> Maybe String
    envpair (n,v) = Just "\{n}=\{v}"

||| Like `execve` but uses the environment of the current process.
export %inline
execv : String -> CArrayIO m (Maybe String) -> EPrim ()
execv s a = toUnit $ prim__execv s (unsafeUnwrap a)

||| Like `execv` but allows us to just use a filename
||| and resolve in using the `$PATH` variable.
export %inline
execvp : String -> CArrayIO m (Maybe String) -> EPrim ()
execvp s a = toUnit $ prim__execvp s (unsafeUnwrap a)

||| Convenience alias for `execvp` that uses an Idris list for
||| the list of arguments.
export
execlp : String -> List String -> EPrim ()
execlp s a w =
  let MkIORes args w := toPrim (fromListIO (map Just a ++ [Nothing])) w
      R res  w       := execvp s args w | E x w => E x w
      MkIORes _    w := toPrim (free args) w
   in R res w

||| Runs the given shell command in a child process.
|||
||| This has a slightly different type signature that the actual
||| `system` call in C, which allows us to use the same mechanism
||| as with `wait` to get the returned exit status.
export %inline
system : (cmd : String) -> EPrim ProcStatus
system cmd = toVal procStatus $ prim__system cmd

||| Waits for one of the child processes of this process to
||| terminate.
|||
||| On success, this returns the process ID of the child process
||| that terminated. In addition, the termination status of the child
||| is written into the given pointer.
export %inline
wait_ : IOBox CInt -> EPrim PidT
wait_ s = toPidT $ prim__wait (unsafeUnwrap s)

||| Waits for the given child processes of to terminate.
|||
||| Unlike `wait`, this allows us to wait on a specific child process.
||| In addition, it is possible to be notified about child processes that have
||| been terminated by a signal.
export %inline
waitpid_ : PidT -> IOBox CInt -> WaitFlags -> EPrim PidT
waitpid_ chld s (F f) = toPidT $ prim__waitpid chld (unsafeUnwrap s) f

||| More powerful version of `waitpid` supporting additional flags and
||| waiting on groups of children. Wait results are stored in the
||| provided `SiginfoT` pointer.
export %inline
waitid_ : IdType -> PidT -> SiginfoT -> WaitFlags -> EPrim ()
waitid_ t chld s (F f) =
  toUnit $ prim__waitid (idtypeCode t) chld (unwrap s) f

--------------------------------------------------------------------------------
-- Convenience API
--------------------------------------------------------------------------------

||| Convenience version of `wait_`.
export %inline
wait : EPrim (PidT, ProcStatus)
wait =
  withBox CInt $ \box,w =>
    let R r w := wait_ box w | E x r => E x r
        MkIORes c w := primRun (unbox box) w
     in R (r, procStatus c) w

||| Convenience version of `waitpid_`.
export %inline
waitpid : PidT -> WaitFlags -> EPrim (PidT, ProcStatus)
waitpid pid flags =
  withBox CInt $ \box,w =>
    let R r w := waitpid_ pid box flags w | E x r => E x r
        MkIORes c w := primRun (unbox box) w
     in R (r, procStatus c) w

||| Convenience version of `waitid_`.
export %inline
waitid : IdType -> PidT -> WaitFlags -> EPrim Siginfo
waitid t pid fs =
  withStruct SiginfoT $ \ss,w =>
    let R _ w := waitid_ t pid ss fs w | E x w => E x w
        MkIORes si w := siginfo ss w
     in R si w
