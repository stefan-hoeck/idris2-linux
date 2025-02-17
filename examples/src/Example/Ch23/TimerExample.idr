module Example.Ch23.TimerExample

import Data.C.Ptr
import Data.IORef
import Data.String

import Example.Util.Opts
import Example.Util.Signal
import Example.Util.Timer

import System.Clock

%default total

usage : String
usage =
  """
  Usage: linux-examples timer_example [secs [usecs [int-secs [int-usecs]]]]

  Sets up and observes a (possibly repeating) timer.
  """

prettyClock : Clock t -> String
prettyClock cl =
  let ns  := nanoseconds cl `div` 10_000_000
      nss := padLeft 2 '0' (show ns)
   in padLeft 7 ' ' "\{show $ seconds cl}.\{nss}"

timeval : TimeT -> SusecondsT -> String
timeval s u =
  let us := padLeft 3 '0' (show $ u `div` 1000)
   in padLeft 10 ' ' "\{show s}.\{us}"


parameters {auto has : Has Errno es}
           {auto haa : Has ArgErr es}
           (calls    : IORef Nat)
           (start    : Clock Monotonic)

  displayTimes : String -> Bool -> Prog es ()
  displayTimes pre includeTimer = do
    now <- liftIO (clockTime Monotonic)
    cs  <- readIORef calls
    modifyIORef calls S
    when ((cast {to = Integer} cs `mod` 20) == 0)
      (stdoutLn "       Elapsed     Value  Interval")

    stdout "\{pre} \{prettyClock $ timeDifference now start}"

    when includeTimer $ do
      TRV (TV is iu) (TV s u) <- getTimer ITIMER_REAL
      stdout "\{timeval s u}\{timeval is iu}"

    stdout "\n"

  covering
  inner : Nat -> ClockT -> Prog es Nat
  inner 0     cl = stdoutLn "That's all folks" $> 0
  inner (S k) cl = do
    now <- clock
    case (((now - cl) * 10) `div` CLOCKS_PER_SEC) < 5 of
      False => pure (S k)
      True  =>
        sigpending >>= \ss => case SIGALRM `elem` ss of
          False => inner (S k) cl
          True  => do
            _ <- sigwaitinfo ss
            displayTimes "ALARM:" True
            inner k cl

  covering
  outer : Nat -> ClockT -> Prog es ()
  outer 0 cl = pure ()
  outer n cl = do
    n2  <- inner n cl
    cl2 <- clock
    when (n2 > 0) (displayTimes "Main: " True)
    outer n2 cl2

covering
app : Has Errno es => Has ArgErr es => (s,u,is,iu : String) -> Prog es ()
app s u is iu = do
  s  <- readOptIO OTime  s
  u  <- readOptIO OUTime u
  is <- readOptIO OTime  is
  iu <- readOptIO OUTime iu
  sigprocmask SIG_BLOCK [SIGALRM]
  setTimer ITIMER_REAL (TRV (TV is iu) (TV s u))
  cl <- clock
  start <- liftIO (clockTime Monotonic)
  calls <- newIORef Z
  displayTimes calls start "START:" False
  outer calls start (if is == 0 && iu == 0 then 1 else 3) cl

export covering
timerExample : Has Errno es => Has ArgErr es => List String -> Prog es ()
timerExample ["--help"]  = stdoutLn usage
timerExample [ ]         = app "2" "0" "0" "0"
timerExample [s]         = app s   "0" "0" "0"
timerExample [s,u]       = app s   u   "0" "0"
timerExample [s,u,is]    = app s   u   is  "0"
timerExample [s,u,is,us] = app s   u   is  us
timerExample args        = throw (WrongArgs usage)
