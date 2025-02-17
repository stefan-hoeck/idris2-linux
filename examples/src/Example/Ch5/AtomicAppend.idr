module Example.Ch5.AtomicAppend

import Data.Buffer
import Example.Util.File
import Example.Util.Opts

%default total

usage : String
usage =
  """
  Usage: linux-examples atomic_append DEST NUM_BYTES [x]

  Appends `NUM_BYTES` bytes to `DEST`, creating it, if it does not
  exist yet. In case of `x` being provided, this omits the `O_APPEND`
  flag and uses `lseek` to get to the end of the file insted.

  This can be used to demonstrate that with `O_APPEND`, writing to
  a file is an atomic operation, while the combination of `lseek`
  and `write` is not. In order to do so, try the following with
  and without the optional `x`s:

  linux-examples atomic_append build/out 10000 x & linux-examples atomic_append build/out 10000 x

  Note, how without the `x`s, you are guaranteed to get a file of 20'000 bytes,
  while with the `x`s, the file will be slightly above 10'000 bytes due to
  the race condition between the two processes writing to the file at
  the same time.
  """

parameters {auto hf : Has Errno es}

  appendBytes : Nat -> Fd -> Prog es ()
  appendBytes 0     fd = pure ()
  appendBytes (S k) fd = fwrite fd "A" >> appendBytes k fd

  seekWriteBytes : Nat -> Fd -> Prog es ()
  seekWriteBytes 0     fd = pure ()
  seekWriteBytes (S k) fd = do
    ignore $ lseek fd 0 SEEK_END
    fwrite fd "A"
    seekWriteBytes k fd

  export covering
  atomicProg : Has ArgErr es => List String -> Prog es ()
  atomicProg ["--help"] = stdoutLn usage
  atomicProg [is,ns] = do
    fi <- readOptIO OPath is
    n  <- readOptIO ONat ns
    withFile fi append 0o666 $ appendBytes n
  atomicProg [is,ns,"x"] = do
    fi <- readOptIO OPath is
    n  <- readOptIO ONat ns
    withFile fi (O_WRONLY <+> O_CREAT) 0o666 $ seekWriteBytes n
  atomicProg _ = throw (WrongArgs usage)
