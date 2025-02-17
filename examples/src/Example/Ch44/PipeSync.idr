module Example.Ch44.PipeSync

import Data.Vect
import Example.Util.File
import Example.Util.Opts
import Example.Util.Pretty
import System.Posix.Pipe
import System.Posix.Process
import System

%default total

usage : String
usage =
  """
  Usage: linux-examples pipe_sync NAT

  Forks the given number of children. Every child will inherit a
  pipe that it can close to signal its completion. The parent will
  wait on the pipe's reading end until end of input, in which case it
  knows that all children have completed execution.
  """

parameters {auto he : Has Errno es}
           {auto ha : Has ArgErr es}

  chld : Nat -> Vect 2 Fd -> Prog es ()
  chld n [i,o] = do
    close i
    pid <- getpid
    usleep 10000
    stdoutLn "Child \{show n} (PID=\{show pid}) closing pipe"
    close o

  run : Nat -> Nat -> Vect 2 Fd -> Prog es ()
  run 0     tot [i,o] = do
    close o
    n <- read i String 1
    stdoutLn "Parent ready to go."
  run (S k) tot fds   = do
    0 <- fork | p => run k tot fds
    chld (tot `minus` k) fds

  export covering
  pipeSync : List String -> Prog es ()
  pipeSync ["--help"]  = stdoutLn usage
  pipeSync [s]         = do
    n <- readOptIO ONat s
    fds <- use1 (malloc _ _) $ \r => pipe r >> runIO (withIArray r toVect)
    run n n fds
  pipeSync args        = throw (WrongArgs usage)
