module Example.Util.File

import Data.Vect
import Data.Maybe0
import Data.Array.Index
import Data.Buffer.Core
import Data.C.Ptr

import public Example.Util.Prog
import public System.Posix.File

%default total

export %inline
FileDesc a => Resource a where
  cleanup fd = handleError {e = Errno} prettyErr (close fd)

tryLT : (m,n : Nat) -> Maybe0 (LT m n)
tryLT m n with (m < n) proof eq
  _ | True  = Just0 (ltOpReflectsLT m n eq)
  _ | False = Nothing0

parameters {auto has : Has Errno es}

  export %inline
  fopen : String -> Flags -> Mode -> Prog es Fd
  fopen pth fs m = openFile pth fs m

  export %inline
  withFile : String -> Flags -> Mode -> (Fd -> Prog es a) -> Prog es a
  withFile pth fs m = use1 (fopen pth fs m)

  export
  writeVect :
       {n : _}
    -> {auto _ : SizeOf a}
    -> {auto _ : SetPtr a}
    -> {auto _ : FileDesc fd}
    -> fd
    -> Vect n a
    -> Prog es Bits32
  writeVect fd vs =
    use1 (malloc a n) $ \p => do
      writeVectIO vs p
      writeArr fd p

  export
  writeList :
       {auto _ : SizeOf a}
    -> {auto _ : SetPtr a}
    -> {auto _ : FileDesc fd}
    -> fd
    -> List a
    -> Prog es Bits32
  writeList fd vs = writeVect fd (fromList vs)

  export
  writeVal :
       {auto _ : SizeOf a}
    -> {auto _ : SetPtr a}
    -> {auto _ : FileDesc fd}
    -> fd
    -> a
    -> Prog es Bits32
  writeVal fd v = writeVect fd [v]

  export
  readFile : String -> Bits32 -> Prog es ByteString
  readFile pth buf = withFile pth O_RDONLY 0 (flip read buf)

  export
  readStr : String -> Bits32 -> Prog es String
  readStr pth buf = toString <$> readFile pth buf

  export covering
  writeAll : FileDesc a => a -> ByteString -> Prog es ()
  writeAll fd (BS 0 _) = pure ()
  writeAll fd bs       =
    writeBytes fd bs >>= \m => writeAll fd (drop (cast m) bs)

  export covering %inline
  writeAllStr : FileDesc a => a -> String -> Prog es ()
  writeAllStr fd = writeAll fd . fromString

  export covering
  writeRawAll : FileDesc a => a -> Bits32 -> Buffer -> Bits32 -> Prog es ()
  writeRawAll fd o buf 0 = pure ()
  writeRawAll fd o buf n =
    writeRaw fd buf o n >>= \w => writeRawAll fd (o+w) buf (n-w)

  export covering
  stream :
       {auto fid : FileDesc a}
    -> (fd : a)
    -> (buffer : Bits32)
    -> (ByteString -> Prog es ())
    -> Prog es ()
  stream fd buf run =
    read fd buf >>= \case
      BS 0 _ => pure ()
      bs     => run bs >> stream fd buf run

  export covering
  streamRaw :
       {auto fid : FileDesc a}
    -> (fd : a)
    -> (buffer : Bits32)
    -> (Buffer -> Bits32 -> Prog es ())
    -> Prog es ()
  streamRaw fd sz run = do
    buf <- primIO (prim__newBuf sz)
    go buf

    where
      go : Buffer -> Prog es ()
      go buf =
        readRaw fd buf sz >>= \case
          0 => pure ()
          n => run buf n >> go buf

  export
  readVect :
       {auto _ : SizeOf a}
    -> {auto _ : Deref a}
    -> {auto _ : FileDesc fd}
    -> fd
    -> (n      : Nat)
    -> Prog es (Vect n a)
  readVect fd n =
    use1 (malloc a n) $ \p => do
      bs <- readArr fd p
      if bs < cast (n * sizeof a)
        then fail EINVAL
        else readVectIO p

  export
  readVal :
       {0 fd   : Type}
    -> {auto _ : SizeOf a}
    -> {auto _ : Deref a}
    -> {auto _ : FileDesc fd}
    -> fd
    -> Prog es a
  readVal fd = head <$> readVect fd 1
