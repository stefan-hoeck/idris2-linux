module Example.Ch4.Tee

import Example.Util.File
import Example.Util.Opts

%default total

usage : String
usage =
  """
  Usage: linux-examples tee [-a] DEST

  Set `$LI_BUF_SIZE` to change the used buffer size (default: 1024).
  """

parameters {auto ha : Has ArgErr es}
           {auto hf : Has Errno es}

  covering
  run : Flags -> String -> Prog es ()
  run fs dst = do
    fo  <- readOptIO OPath dst
    buf <- parseEnv OBits32 "LI_BUF_SIZE" 1024
    withFile fo fs 0o666 $ \fd =>
      stream Stdin buf $ \bs =>
        writeAll fd bs >> writeAll Stdout bs

  export covering
  tee : List String -> Prog es ()
  tee ["--help"] = putStrLn "Usage: \{usage}"
  tee [dst]      = run create dst
  tee ["-a",dst] = run append dst
  tee _          = fail (WrongArgs usage)
