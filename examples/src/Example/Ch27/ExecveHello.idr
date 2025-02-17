module Example.Ch27.ExecveHello

import Data.Linear.Traverse1
import Example.Util.Opts
import Example.Util.File
import System

%default total

usage : String
usage =
  """
  Usage: linux-examples execve_hello

  Prints command-line args and environment.
  """

covering
run : Has Errno es => List String -> Prog es ()
run as = do
  for_ (zipWithIndex as) $ \(n,s) => stdoutLn "args[\{show n}] = \{s}"
  for_ !getEnvironment $ \(n,s)   => stdoutLn "\{n}=\{s}"

export covering
execveHello : Has Errno es => Has ArgErr es => List String -> Prog es ()
execveHello ["--help"] = stdoutLn usage
execveHello _          = getArgs >>= run
