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
run : HasIO io => List String -> io ()
run as = do
  for_ (zipWithIndex as) $ \(n,s) => putStrLn "args[\{show n}] = \{s}"
  for_ !getEnvironment $ \(n,s) => putStrLn "\{n}=\{s}"

export covering
execveHello : Has ArgErr es => List String -> Prog es ()
execveHello ["--help"] = putStrLn "\{usage}"
execveHello _          = getArgs >>= run
