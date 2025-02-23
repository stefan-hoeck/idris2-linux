module Example.Ch57.DgramServer

import Example.Util.File
import Example.Util.Opts
import System.Posix.Socket

%default total

usage : String
usage =
  """
  Usage: linux-examples dgram-server

  Starts a basic sequential data-gram server that echos all input from
  clients, converting strings to upper case.
  """

parameters {auto has : Has Errno es}
           {auto haa : Has ArgErr es}

  covering
  serve : Socket AF_UNIX -> SockaddrUn -> Prog es ()
  serve srv addr = do
    bs  <- recvFrom srv ByteString 4096 0 addr
    pth <- runIO (path addr)
    stdoutLn "Got \{show bs.size} bytes of data from \{pth}"
    _   <- sendto srv (toUpper bs) 0 addr
    serve srv addr

covering
app : Has Errno es => Has ArgErr es => (pth : String) -> Prog es ()
app pth = do
  onErrno ENOENT (pure ()) (unlink pth)
  srv <- socket AF_UNIX SOCK_DGRAM
  bind srv pth
  onErrno
    EINTR
    (stdoutLn "Server interrupted.")
    (puse1 (allocStruct _) (serve srv))

export covering
dgramServer : Has Errno es => Has ArgErr es => List String -> Prog es ()
dgramServer ["--help"] = stdoutLn usage
dgramServer []         = app "/tmp/ud_ucase"
dgramServer args       = throw (WrongArgs usage)
