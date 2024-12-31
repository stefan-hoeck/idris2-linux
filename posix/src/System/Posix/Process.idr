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
setuid : ErrIO io => UidT -> io ()
setuid = eprim . P.setuid

||| Tries to set the effective user ID of the current process
export %inline
seteuid : ErrIO io => UidT -> io ()
seteuid = eprim . P.seteuid

||| Tries to set the real group ID of the current process
export %inline
setgid : ErrIO io => GidT -> io ()
setgid = eprim . P.setgid

||| Tries to set the effective group ID of the current process
export %inline
setegid : ErrIO io => GidT -> io ()
setegid = eprim . P.setegid

parameters {auto eoi : ErrIO io}

  ||| Creates a new child process.
  |||
  ||| This creates a new process by copying the stack, head, and
  ||| data memory segment of the parent process. If successful,
  ||| the functions returns `0` for the child process and
  ||| the child's process ID for the parent.
  export %inline
  fork : io PidT
  fork = eprim P.fork

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
    -> io ()
  execve s a = eprim . P.execve s a

  ||| Convenience alias of `execve` that uses Idris lists for passing
  ||| the arguments list and environment.
  export
  execle : String -> List String -> List (String,String) -> io ()
  execle s a = eprim . P.execle s a

  ||| Like `execve` but uses the environment of the current process.
  export %inline
  execv : String -> CArrayIO m (Maybe String) -> io ()
  execv s = eprim . P.execv s

  ||| Like `execv` but allows us to just use a filename
  ||| and resolve in using the `$PATH` variable.
  export %inline
  execvp : String -> CArrayIO m (Maybe String) -> io ()
  execvp s = eprim . P.execvp s

  ||| Convenience alias for `execvp` that uses an Idris list for
  ||| the list of arguments.
  export
  execlp : String -> List String -> io ()
  execlp s = eprim . P.execlp s

  ||| Runs the given shell command in a child process.
  |||
  ||| This has a slightly different type signature that the actual
  ||| `system` call in C, which allows us to use the same mechanism
  ||| as with `wait` to get the returned exit status.
  export %inline
  system : (cmd : String) -> io ProcStatus
  system = eprim . P.system

  ||| Waits for one of the child processes of this process to
  ||| terminate.
  |||
  ||| On success, this returns the process ID of the child process
  ||| that terminated plus its termination status.
  export %inline
  wait : io (PidT, ProcStatus)
  wait = eprim P.wait

  ||| Waits for the given child processes of to terminate.
  |||
  ||| Unlike `wait`, this allows us to wait on a specific child process.
  ||| In addition, it is possible to be notified about child processes that have
  ||| been terminated by a signal.
  export %inline
  waitpid : PidT -> WaitFlags -> io (PidT, ProcStatus)
  waitpid chld = eprim . P.waitpid chld

  ||| More powerful version of `waitpid` supporting additional flags and
  ||| waiting on groups of children. Wait results are stored in a `Siginfo`
  ||| record.
  export %inline
  waitid : IdType -> PidT -> WaitFlags -> io Siginfo
  waitid t chld = eprim . P.waitid t chld
