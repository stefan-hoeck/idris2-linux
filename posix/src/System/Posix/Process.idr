module System.Posix.Process

import System.Posix.File
import System.Posix.Signal
import System.Posix.Process.Prim as P

import public Data.C.Ptr
import public System.Posix.Errno
import public System.Posix.Process.Flags
import public System.Posix.Process.ProcStatus

%default total

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Returns the process ID of the current process
export %inline
getpid : HasIO io => io PidT
getpid = primIO getpid

||| Returns the process ID of the current process' parent process
export %inline
getppid : HasIO io => io PidT
getppid = primIO getppid

||| Returns the real user ID of the current process
export %inline
getuid : HasIO io => io UidT
getuid = primIO getuid

||| Returns the effective user ID of the current process
export %inline
geteuid : HasIO io => io UidT
geteuid = primIO geteuid

||| Returns the real group ID of the current process
export %inline
getgid : HasIO io => io GidT
getgid = primIO getgid

||| Returns the effective group ID of the current process
export %inline
getegid : HasIO io => io GidT
getegid = primIO getegid

||| Tries to set the real user ID of the current process
export %inline
setuid : Has Errno es => EIO1 f => UidT -> f es ()
setuid u = elift1 (P.setuid u)

||| Tries to set the effective user ID of the current process
export %inline
seteuid : Has Errno es => EIO1 f => UidT -> f es ()
seteuid u = elift1 (P.seteuid u)

||| Tries to set the real group ID of the current process
export %inline
setgid : Has Errno es => EIO1 f => GidT -> f es ()
setgid g = elift1 (P.setgid g)

||| Tries to set the effective group ID of the current process
export %inline
setegid : Has Errno es => EIO1 f => GidT -> f es ()
setegid g = elift1 (P.setegid g)

parameters {auto has : Has Errno es}
           {auto eoi : EIO1 f}

  ||| Creates a new child process.
  |||
  ||| This creates a new process by copying the stack, head, and
  ||| data memory segment of the parent process. If successful,
  ||| the functions returns `0` for the child process and
  ||| the child's process ID for the parent.
  export %inline
  fork : f es PidT
  fork = elift1 P.fork

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
    -> f es ()
  execve s a env = elift1 (P.execve s a env)

  ||| Convenience alias of `execve` that uses Idris lists for passing
  ||| the arguments list and environment.
  export
  execle : String -> List String -> List (String,String) -> f es ()
  execle s a ps = elift1 (P.execle s a ps)

  ||| Like `execve` but uses the environment of the current process.
  export %inline
  execv : String -> CArrayIO m (Maybe String) -> f es ()
  execv s arr = elift1 (P.execv s arr)

  ||| Like `execv` but allows us to just use a filename
  ||| and resolve in using the `$PATH` variable.
  export %inline
  execvp : String -> CArrayIO m (Maybe String) -> f es ()
  execvp s arr = elift1 (P.execvp s arr)

  ||| Convenience alias for `execvp` that uses an Idris list for
  ||| the list of arguments.
  export
  execlp : String -> List String -> f es ()
  execlp s ss = elift1 (P.execlp s ss)

  ||| Runs the given shell command in a child process.
  |||
  ||| This has a slightly different type signature that the actual
  ||| `system` call in C, which allows us to use the same mechanism
  ||| as with `wait` to get the returned exit status.
  export %inline
  system : (cmd : String) -> f es ProcStatus
  system cmd = elift1 (P.system cmd)

  ||| Waits for one of the child processes of this process to
  ||| terminate.
  |||
  ||| On success, this returns the process ID of the child process
  ||| that terminated plus its termination status.
  export %inline
  wait : f es (PidT, ProcStatus)
  wait = elift1 P.wait

  ||| Waits for the given child processes of to terminate.
  |||
  ||| Unlike `wait`, this allows us to wait on a specific child process.
  ||| In addition, it is possible to be notified about child processes that have
  ||| been terminated by a signal.
  export %inline
  waitpid : PidT -> WaitFlags -> f es (PidT, ProcStatus)
  waitpid chld fs = elift1 (P.waitpid chld fs)

  ||| More powerful version of `waitpid` supporting additional flags and
  ||| waiting on groups of children. Wait results are stored in a `Siginfo`
  ||| record.
  export %inline
  waitid : IdType -> PidT -> WaitFlags -> f es Siginfo
  waitid t chld fs = elift1 (P.waitid t chld fs)
