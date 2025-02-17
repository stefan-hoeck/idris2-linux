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

parameters {auto has : Has Errno es}
           {auto haa : Has ArgErr es}
           (efd      : Epollfd)
           (tfd      : Timerfd)
           (sfd      : Signalfd)
           (events   : CArrayIO 2 SEpollEvent)
           (start    : Clock Monotonic)

  covering
  loop : Prog es ()
  loop = do
    es <- epollWaitVals efd events (-1)
    go es

    where
      covering readStdin : Prog es ()
      readStdin = do
        onErrno EAGAIN (stdoutLn "Stdin temporarily exhausted") $ do
          bs <- read Stdin ByteString 4
          stdoutLn "got \{show bs.size} bytes from stdin"
          readStdin

      go : List EpollEvent -> Prog es ()
      go []     = loop
      go (E ev fd ::t) = do
        case fd == cast tfd of
          False => case fd == cast sfd of
            True  => stdoutLn "Got SIGINT. Terminating now."
            False => case fd == cast Stdin of
              True => readStdin >> go t
              False => stdoutLn "Unknown file descriptor: \{show fd}" >> go t
          True  => do
            now <- liftIO (clockTime Monotonic)
            x   <- readTimerfd tfd
            stdoutLn "\{prettyClock now start}: \{show x} tick(s)"
            go t

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
app : Has Errno es => Has ArgErr es => (t : String) -> Prog es ()
app t = do
  sigprocmask SIG_SETMASK [SIGINT]
  ts <- readSpec t
  use
    [ epollCreate 0
    , timerfd CLOCK_MONOTONIC 0
    , signalfd [SIGINT] 0
    , malloc SEpollEvent 2
    ] $ \[efd,tfd,sfd,events] => do
           setTime tfd 0 ts
           addFlags Stdin O_NONBLOCK
           epollCtl efd Add tfd   EPOLLIN
           epollCtl efd Add sfd   EPOLLIN
           epollCtl efd Add Stdin (EPOLLIN <+> EPOLLET)
           start <- liftIO (clockTime Monotonic)
           loop efd tfd sfd events start

export covering
epollExample : Has Errno es => Has ArgErr es => List String -> Prog es ()
epollExample ["--help"] = stdoutLn usage
epollExample [s]        = app s
epollExample args       = throw (WrongArgs usage)
