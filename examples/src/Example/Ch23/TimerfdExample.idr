module Example.Ch23.TimerfdExample

import Data.C.Ptr
import Data.IORef
import Data.List1
import Data.String

import Example.Util.Opts
import Example.Util.Signal
import Example.Util.Timer

import System.Clock

%default total

usage : String
usage =
  """
  Usage: linux-examples timerfd_example secs[/nsecs][:int-secs[/int-nsecs]] [max-exp]

  Sets up and observes a (possibly repeating) timer via a file descriptor.
  """

prettyClock : Clock t -> Clock t -> String
prettyClock now start =
  let cl  := timeDifference now start
      ns  := nanoseconds cl `div` 10_000_000
      nss := padLeft 2 '0' (show ns)
   in padLeft 7 ' ' "\{show $ seconds cl}.\{nss}"

expirations : Bits64 -> String
expirations now =
  let s := padLeft 4 ' ' $ show now
   in "expirations read: \{s}"

tot : Nat -> Nat -> Bits64 -> String
tot exp rem now =
  let s := padLeft 4 ' ' $ show ((exp `minus` rem) + cast now)
   in "total: \{s}"

parameters {auto has : Has Errno es}
           {auto haa : Has ArgErr es}
           (exp      : Nat)
           (fd       : Timerfd)
           (start    : Clock Monotonic)

  covering
  loop : (rem : Nat) -> Prog es ()
  loop 0 = pure ()
  loop n = do
    x   <- readTimerfd fd
    now <- liftIO (clockTime Monotonic)
    stdoutLn "\{prettyClock now start}: \{expirations x}; \{tot exp n x}"
    loop (n `minus` cast x)

readPair : Has ArgErr es => String -> Prog es (TimeT, NsecT)
readPair s =
  case forget $ split ('/' ==) s of
    [x]   => (,0) <$> readOptIO OTime x
    [x,y] => [| MkPair (readOptIO OTime x) (readOptIO ONsecT y) |]
    _     => throw (WrongArgs usage)

readSpec : Has Errno es => Has ArgErr es => String -> Prog es Timerspec
readSpec s =
  case forget $ split (':' ==) s of
    [x]   => do
      fd    <- timerfd CLOCK_MONOTONIC 0
      (s,n) <- readPair x
      pure $ TS (duration 0 0) (duration s n)
    [x,y] => do
      fd    <- timerfd CLOCK_MONOTONIC 0
      (s,n)   <- readPair x
      (si,ni) <- readPair y
      pure $ TS (duration si ni) (duration s n)
    _     => throw (WrongArgs usage)

covering
app : Has Errno es => Has ArgErr es => (t,exp : String) -> Prog es ()
app t exps = do
  exp  <- readOptIO ONat exps
  puse [timerfd CLOCK_MONOTONIC 0] $ \[fd] => do
  ts <- readSpec t
  setTime fd 0 ts
  start <- liftIO (clockTime Monotonic)
  loop exp fd start exp

export covering
timerfdExample : Has Errno es => Has ArgErr es => List String -> Prog es ()
timerfdExample ["--help"]  = stdoutLn usage
timerfdExample [s]         = app s "1"
timerfdExample [s,m]       = app s m
timerfdExample args        = throw (WrongArgs usage)

