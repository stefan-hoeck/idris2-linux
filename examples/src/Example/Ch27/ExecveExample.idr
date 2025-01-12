module Example.Ch27.ExecveExample

import Data.C.Ptr
import Example.Util.Opts
import Example.Util.Dir
import Example.Util.File
import System.Posix.Process

%default total

usage : String
usage =
  """
  Usage: linux-examples execve_example

  Replaces this process with another one.
  """

args : List String
args = ["linux-examples", "execve_hello", "hello world", "goodbye"]

env : List (String,String)
env = [("GREET","salut"), ("BYE","adieu")]

export
execveExample : Has Errno es => Has ArgErr es => List String -> Prog es ()
execveExample ["--help"]  = stdoutLn usage
execveExample []          = do
  p <- getcwd {r = String}
  execle"\{p}/examples/build/exec/linux-examples" args env
execveExample args        = fail (WrongArgs usage)
