module Example.Ch4.Copy

import Example.Util.File
import Example.Util.Opts

%default total

usage : String
usage =
  """
  Usage: linux-examples copy SOURCE DEST [raw]

  Set `$LI_BUF_SIZE` to change the used buffer size (default: 65536).

  The `raw` options uses `readRaw` and `writeRaw` internally without
  reallocating a new buffer on every read. This allows us to get an idea
  of the cost of using immutable `ByteString`s versus reusing the same
  raw buffer. Spoiler: For small files (up to around 100 MB) the cost
  is very small. For larger files, reusing the same buffer starts to
  pay off probably due to garbage collection setting in in the other case.

  Note: To use this in a pipe, set SOURCE to /dev/stdin and/or
        DEST to /dev/stdout.
  """

parameters {auto hf : Has Errno es}

  covering
  copyRaw : FileDesc a => FileDesc b => Bits32 -> a -> b -> Prog es ()
  copyRaw buf i o = streamRaw i buf (writeRawAll o)

  covering
  copy : FileDesc a => FileDesc b => Bits32 -> a -> b -> Prog es ()
  copy buf i o = stream i buf (writeAll o)

  covering
  cpRaw : Bits32 -> String -> String -> Prog es ()
  cpRaw buf i o =
    withFile i 0 0 $ \fi => withFile o create 0o660 $ \fo => copyRaw buf fi fo

  covering
  cp : Bits32 -> String -> String -> Prog es ()
  cp buf i o =
    withFile i 0 0 $ \fi => withFile o create 0o660 $ \fo => copy buf fi fo

  export covering
  copyProg : Has ArgErr es => List String -> Prog es ()
  copyProg ["--help"] = stdoutLn usage
  copyProg [i,o] = do
    fi  <- readOptIO OPath i
    fo  <- readOptIO OPath o
    buf <- parseEnv OBits32 "LI_BUF_SIZE" 0x10000
    cp buf fi fo
  copyProg [i,o,"raw"] = do
    fi  <- readOptIO OPath i
    fo  <- readOptIO OPath o
    buf <- parseEnv OBits32 "LI_BUF_SIZE" 0x10000
    cpRaw buf fi fo
  copyProg _ = fail (WrongArgs usage)
