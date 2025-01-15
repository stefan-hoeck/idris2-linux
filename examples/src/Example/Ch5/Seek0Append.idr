module Example.Ch5.Seek0Append

import Data.Buffer
import Example.Util.File
import Example.Util.Opts

%default total

usage : String
usage =
  """
  Usage: linux-examples seek0_append DEST

  Opens `DEST` with `O_APPEND` and writes "hello world" to `DEST`
  after setting the file offset to zero. This demonstrates, that
  writes to a file opened with `O_APPEND` *always* (and atomically!)
  happen at the end of the file.

  See also program `atomic_append`.
  """

parameters {auto hf : Has Errno es}

  seekWriteBytes : Fd -> Prog es ()
  seekWriteBytes fd = do
    ignore $ lseek fd 0 SEEK_SET
    fwrite fd "hello world"

  export covering
  seekAppendProg : Has ArgErr es => List String -> Prog es ()
  seekAppendProg ["--help"] = stdoutLn usage
  seekAppendProg [is] = do
    fi <- readOptIO OPath is
    withFile fi append 0o666 seekWriteBytes
  seekAppendProg _ = fail (WrongArgs usage)
