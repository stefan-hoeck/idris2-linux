module Example.Ch4.Copy

import Example.Util.File
import Example.Util.Opts

%default total

usage : String
usage =
  """
  Usage: linux-examples copy SOURCE DEST

  Set `$LI_BUF_SIZE` to change the used buffer size (default: 65536).

  Note: To use this in a pipe, set SOURCE to /dev/stdin and/or
        DEST to /dev/stdout.
  """

parameters {auto hf : Has FileErr es}

  export covering
  copy : FileDesc a => FileDesc b => Bits32 -> a -> b -> Prog es ()
  copy buf i o = stream i buf (writeAll o)

  export covering
  cp : Bits32 -> FilePath -> FilePath -> Prog es ()
  cp buf i o =
    withFile i 0 0 $ \fi => withFile o create 0o660 $ \fo => copy buf fi fo

  export covering
  copyProg : Has ArgErr es => List String -> Prog es ()
  copyProg ["--help"] = putStrLn "\{usage}"
  copyProg [i,o] = do
    fi  <- readOptIO OPath i
    fo  <- readOptIO OPath o
    buf <- parseEnv OBits32 "LI_BUF_SIZE" 0x10000
    cp buf fi fo
  copyProg _ = fail (WrongArgs usage)
