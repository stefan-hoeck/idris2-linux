module Example.Ch24.ForkExample

import Data.C.Ptr
import Data.IORef
import Example.Util.Opts
import Example.Util.Prog
import Example.Util.Signal
import System.Posix.Errno
import System.Posix.Process
import System

%default total

usage : String
usage =
  """
  Usage: linux-examples fork_example

  Forks a child process and performs a couple of tests
  """

parameters {auto has : Has Errno es}
           {auto haa : Has ArgErr es}
           (ss       : SigsetT)
           (si       : SiginfoT)
           (status   : Box ProcStatus)

  child : PidT -> IORef Nat -> Prog es ()
  child prnt x = do
    p <- getpid
    stdoutLn "[ child ] was successfully spawned (PID: \{show p})."
    stdoutLn "[ child ] multiplying mutable ref with 3"
    modifyIORef x (*3)
    v <- readIORef x
    stdoutLn "[ child ] mutable ref is at \{show v} now"
    stdoutLn "[ child ] now signalling parent"
    kill prnt SIGUSR1
    stdoutLn "[ child ] awaiting parent to do its work"
    sigwaitinfo ss si
    stdoutLn "[ child ] got informed by parent"
    exitWith (ExitFailure 10)

  parent : PidT -> IORef Nat -> Prog es ()
  parent p x = do
    stdoutLn "[ parent ] spawned a child with PID \{show p}"
    stdoutLn "[ parent ] multiplying mutable ref with 5"
    modifyIORef x (*5)
    v <- readIORef x
    stdoutLn "[ parent ] mutable ref is at \{show v} now"
    stdoutLn "[ parent ] awaiting child to do its work"
    sigwaitinfo ss si
    stdoutLn "[ parent ] got informed by child"
    stdoutLn "[ parent ] now signalling child"
    kill p SIGUSR1
    stdoutLn "[ parent ] waiting for child to finish"
    chld <- wait status
    st   <- unboxIO status
    stdoutLn "[ parent ] child \{show chld} exited with status \{show $ exitstatus st}"

  forkTest : Prog es ()
  forkTest = do
    sigaddset ss SIGUSR1
    sigprocmask' SIG_SETMASK ss
    prnt <- getpid
    ref <- newIORef (S 110)
    fork >>= \case
      0 => child prnt ref
      p => parent p ref

export
forkExample : Has Errno es => Has ArgErr es => List String -> Prog es ()
forkExample ["--help"]  = stdoutLn usage
forkExample []          =
  use [emptySigset, allocStruct _, malloc _ _] $ \[x,y,z] => forkTest x y z
forkExample args        = fail (WrongArgs usage)
