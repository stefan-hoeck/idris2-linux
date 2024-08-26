module CP

import File
import Opts
import System

%default total

usage : String
usage =
  """
  pack test linux copy SOURCE DEST
  """

export covering
copyProg : Has ArgErr es => Has FileErr es => List String -> Prog es ()
copyProg ["--help"] = putStrLn "Usage: \{usage}"
copyProg [i,o] = do
  fi <- readOptIO OPath i
  fo <- readOptIO OPath o
  cp fi fo
copyProg _ = fail (WrongArgs usage)
