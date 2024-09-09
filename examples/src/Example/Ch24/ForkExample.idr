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
           (status   : ProcStatus)

  child : PidT -> IORef Nat -> Prog es ()
  child prnt x = do
    p <- getpid
    putStrLn "[ child ] was successfully spawned (PID: \{show p})."
    putStrLn "[ child ] multiplying mutable ref with 3"
    modifyIORef x (*3)
    v <- readIORef x
    putStrLn "[ child ] mutable ref is at \{show v} now"
    putStrLn "[ child ] now signalling parent"
    injectIO (kill prnt SIGUSR1)
    putStrLn "[ child ] awaiting parent to do its work"
    injectIO (sigwaitinfo ss si)
    putStrLn "[ child ] got informed by parent"
    exitWith (ExitFailure 10)

  parent : PidT -> IORef Nat -> Prog es ()
  parent p x = do
    putStrLn "[ parent ] spawned a child with PID \{show p}"
    putStrLn "[ parent ] multiplying mutable ref with 5"
    modifyIORef x (*5)
    v <- readIORef x
    putStrLn "[ parent ] mutable ref is at \{show v} now"
    putStrLn "[ parent ] awaiting child to do its work"
    injectIO (sigwaitinfo ss si)
    putStrLn "[ parent ] got informed by child"
    putStrLn "[ parent ] now signalling child"
    injectIO (kill p SIGUSR1)
    putStrLn "[ parent ] waiting for child to finish"
    chld <- injectIO (wait status)
    sts  <- exitstatus status
    putStrLn "[ parent ] child \{show chld} exited with status \{show sts}"

  forkTest : Prog es ()
  forkTest = do
    sigaddset ss SIGUSR1
    sigprocmask' SIG_SETMASK ss
    prnt <- getpid
    ref <- newIORef 111
    injectIO fork >>= \case
      0 => child prnt ref
      p => parent p ref

export
forkExample : Has Errno es => Has ArgErr es => List String -> Prog es ()
forkExample ["--help"]  = putStrLn "\{usage}"
forkExample []          =
  use [emptySigset, allocStruct _, allocStruct _] $ \[x,y,z] => forkTest x y z
forkExample args        = fail (WrongArgs usage)
