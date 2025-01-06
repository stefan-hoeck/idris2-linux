module Example.Ch63.EpollPerformance

import Data.C.Ptr
import Data.Linear.Ref1
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
  Usage: linux-examples epoll_performance

  Sets up and observes a signal handler listening on `SIGINT`.
  """

parameters {auto has : Has Errno es}
           (efd      : Epollfd)
           (sfd      : Signalfd)
           (counter  : IORef Nat)
           (events   : CArrayIO 2 SEpollEvent)

  covering
  loop : Prog es ()
  loop = do
    runIO (mod1 counter S)
    es <- epollWaitVals efd events 0
    go es

    where
      go : List EpollEvent -> Prog es ()
      go []            = loop
      go (E ev fd ::t) = do
        case fd == cast sfd of
          True  => do
            n <- runIO (read1 counter)
            stdoutLn "Got SIGINT after \{show n} polls. Terminating now."
          False => stdoutLn "Unknown file descriptor: \{show fd}" >> go t

covering
app : Has Errno es => Prog es ()
app = do
  sigprocmask SIG_SETMASK [SIGINT]
  ref <- newIORef Z
  use
    [ epollCreate 0
    , signalfd [SIGINT] 0
    , malloc SEpollEvent 2
    ] $ \[efd,sfd,events] => do
           epollCtl efd Add sfd EPOLLIN
           loop efd sfd ref events

export covering
epollPerformance : Has Errno es => Has ArgErr es => List String -> Prog es ()
epollPerformance ["--help"] = stdoutLn usage
epollPerformance []         = app
epollPerformance args       = fail (WrongArgs usage)
