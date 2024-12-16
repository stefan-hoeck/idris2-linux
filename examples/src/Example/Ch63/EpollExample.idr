module Example.Ch63.EpollExample

import Data.C.Ptr
import Data.IORef
import Data.List1
import Data.String

import Example.Util.Opts
import Example.Util.Timer

import System.Clock
import System.Linux.Epoll
import System.Linux.Signalfd

%default total

usage : String
usage =
  """
  Usage: linux-examples epoll_example secs[/nsecs][:int-secs[/int-nsecs]]

  Sets up and observes a (possibly repeating) timer via a file descriptor.
  In addition, sets up a file descriptor for listening on `SIGINT`.
  """

prettyClock : Clock t -> Clock t -> String
prettyClock now start =
  let cl  := timeDifference now start
      ns  := nanoseconds cl `div` 10_000_000
      nss := padLeft 2 '0' (show ns)
   in padLeft 7 ' ' "\{show $ seconds cl}.\{nss}"

-- tot : Nat -> Nat -> Bits64 -> String
-- tot exp rem now =
--   let s := padLeft 4 ' ' $ show ((exp `minus` rem) + cast now)
--    in "total: \{s}"
--
parameters {auto has : Has Errno es}
           {auto haa : Has ArgErr es}
           (efd      : Epollfd)
           (tfd      : Timerfd)
           (sfd      : Signalfd)
           (events   : CArrayIO 2 EpollEvent)
           (start    : Clock Monotonic)

  covering
  loop : Prog es ()
  loop = do
    (k ** es) <- epollWait efd events (-1)
    go k es

    where
      go : (k : Nat) -> CArrayIO m EpollEvent -> (0 p : LTE k m) => Prog es ()
      go 0     arr = pure ()
      go (S k) arr = do
        ee <- runIO (getNat arr k)
        f  <- fd ee
        case f == fileDesc tfd of
          False => stdoutLn "Got SIGINT. Terminating now."
          True  => do
            now <- liftIO (clockTime Monotonic)
            x   <- readTimerfd tfd
            stdoutLn "\{prettyClock now start}: \{show x} tick(s)"
            loop

readPair : Has ArgErr es => String -> Prog es (TimeT, NsecT)
readPair s =
  case forget $ split ('/' ==) s of
    [x]   => (,0) <$> readOptIO OTime x
    [x,y] => [| MkPair (readOptIO OTime x) (readOptIO ONsecT y) |]
    _     => fail (WrongArgs usage)

readSpec : Has ArgErr es => String -> Prog es Itimerspec
readSpec s =
  case forget $ split (':' ==) s of
    [x]   => do
      (s,n) <- readPair x
      itimerspec 0 0 s n
    [x,y] => do
      (s,n)   <- readPair x
      (si,ni) <- readPair y
      itimerspec si ni s n
    _     => fail (WrongArgs usage)

covering
app : Has Errno es => Has ArgErr es => (t : String) -> Prog es ()
app t =
  use1 emptySigset $ \fs => do
    sigaddset fs SIGINT
    sigprocmask' SIG_SETMASK fs
    use
      [ epollCreate 0
      , timerfd CLOCK_MONOTONIC 0
      , signalfd fs 0
      , readSpec t
      , malloc EpollEvent 2
      ] $ \[efd,tfd,sfd,it,events] => do
             settime' tfd 0 it
             epollCtl efd Add tfd EPOLLIN
             epollCtl efd Add sfd EPOLLIN
             start <- liftIO (clockTime Monotonic)
             loop efd tfd sfd events start

export covering
epollExample : Has Errno es => Has ArgErr es => List String -> Prog es ()
epollExample ["--help"] = stdoutLn usage
epollExample [s]        = app s
epollExample args       = fail (WrongArgs usage)
