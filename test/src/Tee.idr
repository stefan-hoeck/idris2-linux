module Tee

import File
import Opts

%default total

usage : String
usage =
  """
  pack test linux tee [-a] DEST
  """

parameters {auto ha : Has ArgErr es}
           {auto hf : Has FileErr es}

  covering
  run : Flags -> String -> Prog es ()
  run fs dst = do
    fo <- readOptIO OPath dst
    withFile fo fs 0o666 $ \fd =>
      stream Stdin 0x10000 $ \bs =>
        writeAll fd bs >> writeAll Stdout bs

  export covering
  tee : List String -> Prog es ()
  tee ["--help"] = putStrLn "Usage: \{usage}"
  tee [dst]      = run create dst
  tee ["-a",dst] = run append dst
  tee _          = fail (WrongArgs usage)
