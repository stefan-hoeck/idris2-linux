module Example.Ch44.BasicPipe

import Data.Vect
import Example.Util.File
import Example.Util.Opts
import Example.Util.Pretty
import System.Posix.Pipe
import System.Posix.Process

%default total

usage : String
usage =
  """
  Usage: linux-examples basic_pipe [TEXT]

  Forks a new process and demonstrates basic communication between
  parent and child via a pipe. The child will write a greeting to
  the parent followed by TEXT.
  """

parameters {auto he : Has Errno es}
           {auto ha : Has ArgErr es}

  covering
  prnt : PidT -> Vect 2 Fd -> Prog es ()
  prnt pid [i,o] =
    use1 (cptr 0x1000) $ \cp => do
      close o
      stdoutLn "Spawned child \{show pid}"
      ignore $ streamPtr CPtr i cp (fwrite Stdout)
      close i

  covering
  chld : String -> Vect 2 Fd -> Prog es ()
  chld s [i,o] = do
    close i
    pid <- getpid
    fwrite o "Hello. I'm child number \{show pid}\n"
    fwrite o "Here's the message I got:\n"
    fwrite o "\n  '\{s}'\n"

  covering
  run : String -> Prog es ()
  run s = do
    fds <- use1 (malloc _ _) $ \r => pipe r >> runIO (withIArray r toVect)
    0 <- fork | p => prnt p fds
    chld s fds

  export covering
  basicPipe : List String -> Prog es ()
  basicPipe ["--help"]  = stdoutLn usage
  basicPipe [s]         = run s
  basicPipe args        = fail (WrongArgs usage)
