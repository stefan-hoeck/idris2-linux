module Example.Ch63.PollPerformance

import Data.C.Ptr
import Data.Linear.Ref1
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
  Usage: linux-examples poll_performance

  Sets up and observes a signal handler listening on `SIGINT`.
  """

parameters {auto has : Has Errno es}
           (sfd      : Signalfd)
           (counter  : IORef Nat)
           (events   : CArrayIO 1 PollFD)

  covering
  loop : Prog es ()
  loop = do
    runIO (mod1 counter S)
    es <- poll events 0
    go es

    where
      go : List PollPair -> Prog es ()
      go []            = loop
      go (PP fd ev ::t) = do
        case fd == cast sfd of
          True  => do
            n <- runIO (read1 counter)
            stdoutLn "Got SIGINT after \{show n} polls. Terminating now."
          False => stdoutLn "Unknown file descriptor: \{show fd}" >> go t

covering
app : Has Errno es => Prog es ()
app = do
  sigprocmask SIG_SETMASK [SIGINT]
  ref <- newref Z
  use
    [ signalfd [SIGINT] 0
    , calloc PollFD 1
    ] $ \[sfd,events] => do
           lift1 $ writeFiles events [ PP (cast sfd) POLLIN ]
           loop sfd ref events

export covering
pollPerformance : Has Errno es => Has ArgErr es => List String -> Prog es ()
pollPerformance ["--help"] = stdoutLn usage
pollPerformance []         = app
pollPerformance args       = throw (WrongArgs usage)
