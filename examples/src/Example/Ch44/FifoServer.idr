module Example.Ch44.FifoServer

import Data.Vect
import Example.Util.File
import Example.Util.Opts
import Example.Util.Pretty
import System.Posix.Pipe
import System.Posix.Process

%default total

serverFifo : String
serverFifo = "/tmp/seqnum_sv"

clientFifo : Bits64 -> String
clientFifo n = "/tmp/seqnum_cl.\{show n}"

usage : String
usage =
  """
  Usage: linux-examples fifo_server

  Creates a simple server that reads client requests from /tmp/seqnum_sv
  and responds to a client FIFO with the beginning of a memory region.
  """

clientUsage : String
clientUsage =
  """
  Usage: linux-examples fifo_client NUM

  Requests the start of a memory region of `NUM` bytes from the server.
  """

parameters {auto he : Has Errno es}
           {auto ha : Has ArgErr es}

  tryMkFifo : String -> Prog es ()
  tryMkFifo s = onErrno EEXIST (pure ()) (mkfifo s 0o600)

  covering
  serve : Bits64 -> Fd -> Prog es ()
  serve pos fd = do
    [p,n] <- readVect fd 2
    stdoutLn "Got request from client \{show p}: \{show n} bytes"
    withFile (clientFifo p) O_WRONLY 0 $ \o => fwrite o (the (List _) [pos])
    serve (pos + n) fd

  export covering
  fifoServer : List String -> Prog es ()
  fifoServer ["--help"]  = stdoutLn "\{usage}"
  fifoServer []          = do
    tryMkFifo serverFifo
    use [openFile serverFifo O_RDONLY 0, openFile serverFifo O_WRONLY 0] $
      \[fd,_] => serve 0 fd
  fifoServer args        = fail (WrongArgs usage)

  export
  fifoClient : List String -> Prog es ()
  fifoClient ["--help"]  = stdoutLn usage
  fifoClient [s]         = do
    n   <- readOptIO OBits32 s
    pid <- cast {to = Bits64} <$> getpid
    let pth := clientFifo pid
    tryMkFifo pth
    stdoutLn "Created FIFO at \{pth}"
    stdoutLn "Sending request (PID=\{show pid}) for \{show n} bytes"
    withFile serverFifo O_WRONLY 0 $ \s => fwrite s (the (List _) [pid,cast n])
    stdoutLn "Sent message to server"
    v <- withFile pth O_RDONLY 0 $ \s => readVal {a = Bits64} s
    stdoutLn (show v)


  fifoClient args        = fail (WrongArgs usage)
