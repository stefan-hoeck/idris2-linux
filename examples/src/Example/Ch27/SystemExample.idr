module Example.Ch27.SystemExample

import Data.C.Ptr
import Data.Bits
import Data.String
import Example.Util.Opts
import Example.Util.Dir
import Example.Util.File
import Example.Util.Pretty
import System.Posix.Process

%default total

usage : String
usage =
  """
  Usage: linux-examples system_example

  Runs shell commands given at the command-line.
  """

printStatus : ErrIO io => ProcStatus -> io ()
printStatus (Exited 127) = stdoutLn "(Probably) could not invoke shell"
printStatus s            = stdoutLn $ prettyStatus "" s

covering
loop : Has Errno es => Prog es ()
loop = do
  _   <- stdout "Command: "
  cmd <- read Stdin String 4096
  when (cmd /= "") $ do
    status <- system cmd
    printStatus status
    loop
  stdoutLn "\nGoodbye!"

export covering
systemExample : Has Errno es => Has ArgErr es => List String -> Prog es ()
systemExample ["--help"]  = stdoutLn "\{usage}"
systemExample []          = loop
systemExample args        = fail (WrongArgs usage)
