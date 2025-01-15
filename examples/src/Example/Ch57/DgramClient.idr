module Example.Ch57.DgramClient

import Data.ByteVect
import Data.ByteString
import Example.Util.File
import Example.Util.Opts
import System.Posix.Process
import System.Posix.Socket

%default total

usage : String
usage =
  """
  Usage: linux-examples dgram-client args

  Starts a client that connects to the unix socket at
  `socket_path` (default: `/tmp/le_unix_skt`) and
  echos all input from stdin to the socket.
  """

parameters {auto has : Has Errno es}
           {auto haa : Has ArgErr es}

  covering
  echo : Socket AF_UNIX -> Prog es ()
  echo cli = do
    readres Stdin ByteString 4096 >>= \case
      Interrupted => stdoutLn "Interrupted" >> echo cli
      NoData      => echo cli
      Closed      => stdoutLn "Broken pipe." >> close cli
      EOI         => stdoutLn "End of input." >> close cli
      Res bs      => fwrite cli bs >> echo cli

covering
app : Has Errno es => Has ArgErr es => List String -> Prog es ()
app args = do
  cli <- socket AF_UNIX SOCK_DGRAM
  srv <- runIO (sockaddrUn "/tmp/ud_ucase")
  pid <- getpid
  bind cli "/tmp/ud_ucase_cli.\{show pid}"
  for_ args $ \arg => do
    _  <- sendto cli arg 0 srv
    bs <- recvFrom cli ByteString 128 0 srv
    write Stdout (bs <+> "\n")
  remove "/tmp/ud_ucase_cli.\{show pid}"

export covering
dgramClient : Has Errno es => Has ArgErr es => List String -> Prog es ()
dgramClient ["--help"] = stdoutLn usage
dgramClient args       = app args
