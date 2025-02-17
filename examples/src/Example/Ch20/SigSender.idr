module Example.Ch20.SigSender

import Example.Util.Opts
import System.Posix.File
import System.Posix.Signal
import System

%default total

usage : String
usage =
  """
  Usage: linux-examples sig_send PID num-sigs sig1 [sig2]

  Sends `sig1` `num-sigs` times to the process with process ID `PID`.
  If `sig2` is specified, sends `sig2` once after the other signals have
  been sent.
  """

parameters {auto hf : Has Errno es}

  run : PidT -> Nat -> Signal -> Maybe Signal -> Prog es ()
  run p 0     s m = for_ m $ \s2 => usleep 1000 >> kill p s2
  run p (S k) s m = kill p s >> run p k s m

  app : Has ArgErr es => (p,n,s1 : String) -> Maybe String -> Prog es ()
  app p n s1 s2 = do
    pid  <- readOptIO OPid p
    cnt  <- readOptIO ONat n
    sig  <- readOptIO OSig s1
    sig2 <- traverse (readOptIO OSig) s2
    run pid cnt sig sig2

  export
  sigSend : Has ArgErr es => List String -> Prog es ()
  sigSend ["--help"]  = stdoutLn usage
  sigSend [p,n,s1]    = app p n s1 Nothing
  sigSend [p,n,s1,s2] = app p n s1 (Just s2)
  sigSend args       = throw (WrongArgs usage)
