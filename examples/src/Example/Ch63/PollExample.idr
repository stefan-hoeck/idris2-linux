module Example.Ch63.PollExample

import Data.C.Ptr
import Data.IORef
import Data.List1
import Data.String

import Example.Util.Opts
import Example.Util.Timer

import System.Clock
import System.Posix.Poll
import System.Linux.Signalfd

%default total

usage : String
usage =
  """
  Usage: linux-examples poll_example secs[/nsecs][:int-secs[/int-nsecs]]

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
           (tfd      : Timerfd)
           (sfd      : Signalfd)
           (events   : CArrayIO 3 PollFD)
           (start    : Clock Monotonic)

  covering
  loop : Prog es ()
  loop = do
    es <- poll events (-1)
    go es

    where
      covering readStdin : Prog es ()
      readStdin = do
        onErrno EAGAIN (stdoutLn "Stdin temporarily exhausted") $ do
          bs <- read Stdin ByteString 4
          stdoutLn "got \{show bs.size} bytes from stdin"
          readStdin

      go : List PollPair -> Prog es ()
      go []     = loop
      go (PP fd ev ::t) = do
        case fd == cast tfd of
          False => case fd == cast sfd of
            True  => stdoutLn "Got SIGINT (\{show ev}). Terminating now."
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
    [ timerfd CLOCK_MONOTONIC 0
    , signalfd [SIGINT] 0
    , calloc PollFD 3
    ] $ \[tfd,sfd,events] => do
           setTime tfd 0 ts
           addFlags Stdin O_NONBLOCK
           lift1 $ writeFiles events
             [ PP (cast sfd) POLLIN
             , PP (cast Stdin) POLLIN
             , PP (cast tfd) POLLIN
             ]
           start <- liftIO (clockTime Monotonic)
           loop tfd sfd events start

export covering
pollExample : Has Errno es => Has ArgErr es => List String -> Prog es ()
pollExample ["--help"] = stdoutLn usage
pollExample [s]        = app s
pollExample args       = throw (WrongArgs usage)
