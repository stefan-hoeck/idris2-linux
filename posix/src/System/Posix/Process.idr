module System.Posix.Process

import public Data.C.Ptr
import public System.Posix.Errno
import System.Posix.File
import public System.Posix.Process.Flags
import System.Posix.Signal

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

%foreign "C:li_wifexited, posix-idris"
prim__exited : CInt -> Bits8

%foreign "C:li_wexitstatus, posix-idris"
prim__exitstatus : CInt -> Bits8

%foreign "C:li_wifsignaled, posix-idris"
prim__signaled : CInt -> Bits8

%foreign "C:li_wtermsig, posix-idris"
prim__termsig : CInt -> Bits32

%foreign "C:li_wcoredump, posix-idris"
prim__coredump : CInt -> Bits8

%foreign "C:li_wifstopped, posix-idris"
prim__stopped : CInt -> Bits8

%foreign "C:li_wstopsig, posix-idris"
prim__stopsig : CInt -> Bits32

%foreign "C:li_wifcontinued, posix-idris"
prim__continued : CInt -> Bits8

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

||| Process status returned by a call to `wait` or `waitpid`.
public export
record ProcStatus where
  constructor PS
  status : CInt

public export %inline
SizeOf ProcStatus where
  sizeof_ = sizeof CInt

export %inline
Deref ProcStatus where
  deref = map PS . deref

export %inline
SetPtr ProcStatus where
  setPtr p = setPtr p . status

||| Creates a new child process.
|||
||| This creates a new process by copying the stack, head, and
||| data memory segment of the parent process. If successful,
||| the functions returns `0` for the child process and
||| the child's process ID for the parent.
export %inline
fork : IO (Either Errno PidT)
fork = toPidT Process.prim__fork

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
  -> IO (Either Errno ())
execve s a e = toUnit $ prim__execve s (unsafeUnwrap a) (unsafeUnwrap e)

||| Convenience alias of `execve` that uses Idris lists for passing
||| the arguments list and environment.
export
execle : String -> List String -> List (String,String) -> IO (Either Errno ())
execle s a e = do
  args <- fromListIO (map Just a ++ [Nothing])
  env  <- fromListIO (map envpair e ++ [Nothing])
  res  <- execve s args env
  free args
  free env
  pure res

  where
    envpair : (String,String) -> Maybe String
    envpair (n,v) = Just "\{n}=\{v}"

||| Like `execve` but uses the environment of the current process.
export %inline
execv : String -> CArrayIO m (Maybe String) -> IO (Either Errno ())
execv s a = toUnit $ prim__execv s (unsafeUnwrap a)

||| Like `execv` but allows us to just use a filename
||| and resolve in using the `$PATH` variable.
export %inline
execvp : String -> CArrayIO m (Maybe String) -> IO (Either Errno ())
execvp s a = toUnit $ prim__execvp s (unsafeUnwrap a)

||| Convenience alias for `execvp` that uses an Idris list for
||| the list of arguments.
export
execlp : String -> List String -> IO (Either Errno ())
execlp s a = do
  args <- fromListIO (map Just a ++ [Nothing])
  res  <- execvp s args
  free args
  pure res

||| Runs the given shell command in a child process.
|||
||| This has a slightly different type signature that the actual
||| `system` call in C, which allows us to use the same mechanism
||| as with `wait` to get the returned exit status.
export %inline
system : (cmd : String) -> IO (Either Errno ProcStatus)
system cmd = toVal PS $ prim__system cmd

||| Waits for one of the child processes of this process to
||| terminate.
|||
||| On success, this returns the process ID of the child process
||| that terminated. In addition, the termination status of the child
||| is written into the given pointer.
export %inline
wait : Box ProcStatus -> IO (Either Errno PidT)
wait s = toPidT $ prim__wait (unsafeUnwrap s)

||| Waits for the given child processes of to terminate.
|||
||| Unlike `wait`, this allows us to wait on a specific child process.
||| In addition, it is possible to be notified about child processes that have
||| been terminated by a signal.
export %inline
waitpid : PidT -> Box ProcStatus -> WaitFlags -> IO (Either Errno PidT)
waitpid chld s (F f) = toPidT $ prim__waitpid chld (unsafeUnwrap s) f

||| More powerful version of `waitpid` supporting additional flags and
||| waiting on groups of children. Wait results are stored in the
||| provided `SiginfoT` pointer.
export %inline
waitid : IdType -> PidT -> SiginfoT -> WaitFlags -> IO (Either Errno ())
waitid t chld s (F f) =
  toUnit $ prim__waitid (idtypeCode t) chld (unwrap s) f

%inline
toBool : Bits8 -> Bool
toBool 0 = False
toBool _ = True

||| `True` if the process exited normally.
export %inline
exited : ProcStatus -> Bool
exited s = toBool $ prim__exited s.status

||| Returns the exit status with which the process exited.
export %inline
exitstatus : ProcStatus -> Bits8
exitstatus s = prim__exitstatus s.status

||| `True` if the process has been killed by a signal.
export %inline
signaled : ProcStatus -> Bool
signaled s = toBool $ prim__signaled s.status

||| Returns the signal the process was killed with.
export %inline
termsig : ProcStatus -> Signal
termsig s = S $ prim__termsig s.status

||| `True` if the process has dumped core.
export %inline
coredump : ProcStatus -> Bool
coredump s = toBool $ prim__coredump s.status

||| `True` if the process has been stopped by a signal.
export %inline
stopped : ProcStatus -> Bool
stopped s = toBool $ prim__stopped s.status

||| Returns the signal the process was stopped with.
export %inline
stopsig : ProcStatus -> Signal
stopsig s = S $ prim__stopsig s.status

||| `True` if the process has been awakend with `SIGCONT`.
export %inline
continued : ProcStatus -> Bool
continued s = toBool $ prim__continued s.status
