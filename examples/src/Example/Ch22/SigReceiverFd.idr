||| This is an alternative version of `Ch20.SigReceiver` making
||| use of `signalfd` for signal handling.
module Example.Ch22.SigReceiverFd

import Data.SortedMap
import Data.String
import Data.Finite
import Example.Util.Opts
import Example.Util.Signal
import System
import System.Posix.Process
import System.Linux.Signalfd

%default total

usage : String
usage =
  """
  Usage: linux-examples sig_receive_fd [s]

  Catches and counts all signals until `SIGINT` is caught. Sleeps for `s`
  seconds (default: 0) before starting to catch signals.
  """

parameters {auto hf : Has Errno es}

  covering
  loop : SortedMap Signal Nat -> Signalfd -> CArrayIO 1 SSiginfo -> Prog es ()
  loop cs fd arr = do
    [si] <- readSignalfd fd arr | _ => loop cs fd arr
    case si.signal == SIGINT of
      False => loop (insertWith (+) si.signal 1 cs) fd arr
      True  => do
        stdoutLn "\nGot SIGINT. Signal counts:"
        for_ (SortedMap.toList cs) $ \(s,n) => stdoutLn "\{s}: \{show n}"

  covering
  app : Has ArgErr es => Nat -> Prog es ()
  app n =
    use [malloc SSiginfo 1] $ \[arr] =>
      use1 (signalfd values 0) $ \fd => do
        pid       <- getpid
        stdoutLn "PID: \{show pid}"
        sigprocmask SIG_SETMASK values
        when (n > 0) $ do
          stdoutLn "sleeping for \{show n} seconds"
          sleep (cast n)
          ss <- sigpending
          stdoutLn "pending signals: \{unwords $ map interpolate ss}"

        loop empty fd arr

  export covering
  sigReceiveFd : Has ArgErr es => List String -> Prog es ()
  sigReceiveFd ["--help"] = stdoutLn usage
  sigReceiveFd [s]        = readOptIO ONat s >>= app
  sigReceiveFd []         = app 0
  sigReceiveFd args       = fail (WrongArgs usage)
