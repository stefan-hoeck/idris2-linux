||| This has been adjusted to use the synchronous signal handlers
||| from chapter 22 since all asynchronous versions were flaky on
||| the Chez backend.
module Example.Ch20.SigReceiver

import Data.C.Ptr
import Data.Finite
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
  loop : SortedMap Signal Nat -> Prog es ()
  loop cs = do
    si <- sigwaitinfo values
    case si.signal == SIGINT of
      False => loop $ insertWith (+) si.signal 1 cs
      True  => do
        stdoutLn "\nGot SIGINT. Signal counts:"
        for_ (SortedMap.toList cs) $ \(s,n) => stdoutLn "\{s}: \{show n}"

  covering
  app : Has ArgErr es => Nat -> Prog es ()
  app n = do
    pid <- getpid
    stdoutLn "PID: \{show pid}"
    sigprocmask SIG_SETMASK values
    when (n > 0) $ do
      stdoutLn "sleeping for \{show n} seconds"
      sleep (cast n)
      ss <- sigpending
      stdoutLn "pending signals: \{unwords $ map interpolate ss}"

    loop empty

  export covering
  sigReceive : Has ArgErr es => List String -> Prog es ()
  sigReceive ["--help"] = stdoutLn usage
  sigReceive [s]        = readOptIO ONat s >>= app
  sigReceive []         = app 0
  sigReceive args       = throw (WrongArgs usage)
