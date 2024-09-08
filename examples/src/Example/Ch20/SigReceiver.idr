||| This has been adjusted to use the synchronous signal handlers
||| from chapter 22 since all asynchronous versions were flaky on
||| the Chez backend.
module Example.Ch20.SigReceiver

import Data.C.Ptr
import Data.SortedMap
import Data.String
import Example.Util.Opts
import Example.Util.Signal
import System
import System.Posix.Process

%default total

usage : String
usage =
  """
  Usage: linux-examples sig_receive [s]

  Catches and counts all signals until `SIGINT` is caught. Sleeps for `s`
  seconds (default: 0) before starting to catch signals.
  """

parameters {auto hf : Has Errno es}

  covering
  loop : SortedMap Signal Nat -> SigsetT -> SiginfoT -> Prog es ()
  loop cs set info = do
    injectIO (sigwaitinfo set info)
    sig <- signal info
    case sig == SIGINT of
      False => loop (insertWith (+) sig 1 cs) set info
      True  => do
        putStrLn "\nGot SIGINT. Signal counts:"
        for_ (SortedMap.toList cs) $ \(s,n) => putStrLn "\{s}: \{show n}"

  covering
  app : Has ArgErr es => Nat -> Prog es ()
  app n =
    use [fullSigset, allocStruct SiginfoT] $ \[fs,info] => do
      pid       <- getpid
      putStrLn "PID: \{show pid}"
      sigprocmask' SIG_SETMASK fs
      when (n > 0) $ do
        putStrLn "sleeping for \{show n} seconds"
        sleep (cast n)
        ss <- pendingSignals
        putStrLn "pending signals: \{unwords $ map interpolate ss}"

      loop empty fs info

  export covering
  sigReceive : Has ArgErr es => List String -> Prog es ()
  sigReceive ["--help"] = putStrLn "\{usage}"
  sigReceive [s]        = readOptIO ONat s >>= app
  sigReceive []         = app 0
  sigReceive args       = fail (WrongArgs usage)
