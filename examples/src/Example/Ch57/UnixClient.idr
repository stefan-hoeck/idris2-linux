module Example.Ch57.UnixClient

import Example.Util.File
import Example.Util.Opts
import System.Posix.Socket

%default total

usage : String
usage =
  """
  Usage: linux-examples unix-client [socket_path]

  Starts a client that connects to the unix socket at
  `socket_path` (default: `/tmp/le_unix_skt`) and
  echos all input from stdin to the socket.
  """

parameters {auto has : Has Errno es}
           {auto haa : Has ArgErr es}
           {k        : Nat}
           (arr      : CArrayIO k Bits8)

  covering
  echo : Socket AF_UNIX -> Prog es ()
  echo cli = do
    readArr Stdin arr >>= \case
      (0 ** _)   => close cli
      (n ** dat) => ignore (writeArr cli dat) >> echo cli

covering
app : Has Errno es => Has ArgErr es => (pth : String) -> Prog es ()
app pth =
  use1 (malloc Bits8 4096) $ \arr => do
    cli <- socket AF_UNIX SOCK_STREAM
    connect cli pth
    echo arr cli

export covering
unixClient : Has Errno es => Has ArgErr es => List String -> Prog es ()
unixClient ["--help"] = stdoutLn usage
unixClient []         = app "/tmp/le_unix_skt"
unixClient [s]        = app s
unixClient args       = fail (WrongArgs usage)
