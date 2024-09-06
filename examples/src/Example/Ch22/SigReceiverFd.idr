||| This is an alternative version of `Ch20.SigReceiver` making
||| use of `signalfd` for signal handling.
module Example.Ch22.SigReceiverFd

import Data.SortedMap
import Data.String
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
  loop : SortedMap Signal Nat -> Signalfd -> CArrayIO 1 SiginfoFd -> Prog es ()
  loop cs fd arr = do
    (1 ** p) <- injectIO (readSignalfd fd arr) | _ => loop cs fd arr
    sig <- liftIO (unboxIO p >>= signal)
    case sig == SIGINT of
      False => loop (insertWith (+) sig 1 cs) fd arr
      True  => do
        putStrLn "\nGot SIGINT. Signal counts:"
        for_ (SortedMap.toList cs) $ \(s,n) => putStrLn "\{s}: \{show n}"

  covering
  app : Has ArgErr es => Nat -> Prog es ()
  app n =
    use [fullSigset,IO.malloc SiginfoFd 1] $ \[fs,arr] =>
      use1 (injectIO $ signalfd fs 0) $ \fd => do
        pid       <- getpid
        putStrLn "PID: \{show pid}"
        sigprocmask' SIG_SETMASK fs
        when (n > 0) $ do
          putStrLn "sleeping for \{show n} seconds"
          sleep (cast n)
          ss <- pendingSignals
          putStrLn "pending signals: \{unwords $ map interpolate ss}"

        loop empty fd arr

  export covering
  sigReceiveFd : Has ArgErr es => List String -> Prog es ()
  sigReceiveFd ["--help"] = putStrLn "\{usage}"
  sigReceiveFd [s]        = readOptIO ONat s >>= app
  sigReceiveFd []         = app 0
  sigReceiveFd args       = fail (WrongArgs usage)
