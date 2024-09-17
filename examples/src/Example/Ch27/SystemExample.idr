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
printStatus s =
  let x    := cast {to = Bits64} s.status
      hx   := hex 4 x
      stat := shiftR x 8
      sig  := x .&. 0xff
   in do
     stdoutLn "system() returned: \{hx} (\{show stat}, \{show sig})"
     case exited s && exitstatus s == 127 of
       True  => stdoutLn "(Probably) could not invoke shell"
       False => stdoutLn $ prettyStatus "" s

covering
loop : Has Errno es => Prog es ()
loop = do
  _   <- stdout "Command: "
  cmd <- read Stdin 4096
  when (cmd.size > 0) $ do
    status <- system $ toString cmd
    printStatus status
    loop
  stdoutLn "\nGoodbye!"

export covering
systemExample : Has Errno es => Has ArgErr es => List String -> Prog es ()
systemExample ["--help"]  = stdoutLn "\{usage}"
systemExample []          = loop
systemExample args        = fail (WrongArgs usage)
