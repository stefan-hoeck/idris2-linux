module Example.Ch57.UnixServer

import Example.Util.File
import Example.Util.Opts
import System.Posix.Socket

%default total

usage : String
usage =
  """
  Usage: linux-examples unix-server [socket_path]

  Starts a basic sequential unix server that echos all input from
  clients to stdout. A socket is created a `socket_path`
  (default: `/tmp/le_unix_skt`).
  """

parameters {auto has : Has Errno es}
           {auto haa : Has ArgErr es}

  covering
  echo : Socket AF_UNIX -> Prog es ()
  echo cli = do
    recv cli ByteString 4096 0 >>= \case
      EOI         => stdoutLn "End of input." >> close cli
      Closed      => stdoutLn "Connection closed by peer." >> close cli
      Interrupted => stdoutLn "Read interrupted"
      NoData      => echo cli
      Res bs      => fwrite Stdout bs >> echo cli

  covering
  serve : Socket AF_UNIX -> Prog es ()
  serve srv = do
    onErrno EINTR (stdoutLn "Server interrupted.") $ do
      cli <- accept srv
      stdoutLn "Got a new connection"
      echo cli
      serve srv

covering
app : Has Errno es => Has ArgErr es => (pth : String) -> Prog es ()
app pth = do
  onErrno ENOENT (pure ()) (unlink pth)
  srv <- socket AF_UNIX SOCK_STREAM
  bind srv pth
  listen srv 8
  serve srv

export covering
unixServer : Has Errno es => Has ArgErr es => List String -> Prog es ()
unixServer ["--help"] = stdoutLn usage
unixServer []         = app "/tmp/le_unix_skt"
unixServer [s]        = app s
unixServer args       = fail (WrongArgs usage)
