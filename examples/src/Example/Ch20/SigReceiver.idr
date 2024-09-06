module Example.Ch20.SigReceiver

import Data.Finite
import Data.IORef
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

handler : IORef Bool -> IORef (SortedMap Signal Nat) -> Signal -> IO ()
handler gotSigInt counts s =
  if s == SIGINT
     then writeIORef gotSigInt True
     else modifyIORef counts (insertWith (+) s 1)

covering
loop : IORef Bool -> IORef (SortedMap Signal Nat) -> IO ()
loop gotSigInt counts = do
  True <- readIORef gotSigInt | False => loop gotSigInt counts
  putStrLn "\nGot SIGINT. Signal counts:"
  cs   <- readIORef counts
  for_ (SortedMap.toList cs) $ \(s,n) => putStrLn "\{s}: \{show n}"

parameters {auto hf : Has Errno es}

  covering
  app : Has ArgErr es => Nat -> Prog es ()
  app n =
    withSigset True $ \fs => withSigset False $ \es => do
    pid       <- getpid
    putStrLn "PID: \{show pid}"
    gotSigInt <- newIORef False
    counts    <- newIORef {a = SortedMap Signal Nat} empty
    for_ values $ \s => onsignal s (handler gotSigInt counts)
    when (n > 0) $ do
      sigprocmask' SIG_SETMASK fs
      putStrLn "sleeping for \{show n} seconds"
      sleep (cast n)
      ss <- pendingSignals
      putStrLn "pending signals: \{unwords $ map interpolate ss}"
      sigprocmask' SIG_SETMASK es

    liftIO (loop gotSigInt counts)

  export covering
  sigReceive : Has ArgErr es => List String -> Prog es ()
  sigReceive ["--help"] = putStrLn "\{usage}"
  sigReceive [s]        = readOptIO ONat s >>= app
  sigReceive []         = app 0
  sigReceive args       = fail (WrongArgs usage)
