module Example.Ch24.ForkExample

import Data.C.Ptr
import Data.IORef
import Example.Util.Opts
import Example.Util.Prog
import Example.Util.Signal
import System.Posix.Errno
import System.Posix.Process

%default total

usage : String
usage =
  """
  Usage: linux-examples fork_example

  Forks a child process and performs a couple of tests
  """

parameters {auto has : Has Errno es}
           {auto haa : Has ArgErr es}

  child : SigsetT -> SiginfoT -> PidT -> IORef Nat -> Prog es ()
  child ss si prnt x = do
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

  parent : SigsetT -> SiginfoT -> PidT -> IORef Nat -> Prog es ()
  parent ss si p x = do
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

  forkTest : Prog es ()
  forkTest =
    use [emptySigset, allocStruct SiginfoT] $ \[ss,si] => do
      sigaddset ss SIGUSR1
      sigprocmask' SIG_SETMASK ss
      prnt <- getpid
      ref <- newIORef 111
      injectIO fork >>= \case
        0 => child ss si prnt ref
        p => parent ss si p ref

export
forkExample : Has Errno es => Has ArgErr es => List String -> Prog es ()
forkExample ["--help"]  = putStrLn "\{usage}"
forkExample []          = forkTest
forkExample args        = fail (WrongArgs usage)
