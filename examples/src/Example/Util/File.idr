module Example.Util.File

import Data.Maybe0
import Data.Array.Index
import Data.Buffer.Core
import Data.C.Integer

import public Example.Util.Prog
import public System.Posix.File

%default total

tryLT : (m,n : Nat) -> Maybe0 (LT m n)
tryLT m n with (m < n) proof eq
  _ | True  = Just0 (ltOpReflectsLT m n eq)
  _ | False = Nothing0

export
tryClose : FileDesc a => a -> Prog fs ()
tryClose fd = handleError prettyErr (wrapIO $ close fd)

parameters {auto has : Has Errno es}

  export
  withFile : String -> Flags -> Mode -> (Fd -> Prog es a) -> Prog es a
  withFile pth fs m run = do
    fd <- injectIO $ openFile pth fs m
    finally (tryClose fd) (run fd)

  export
  readFile : String -> Bits32 -> Prog es ByteString
  readFile pth buf =
    withFile pth O_RDONLY 0 (\x => injectIO (read x buf))

  export
  readStr : String -> Bits32 -> Prog es String
  readStr pth buf = toString <$> readFile pth buf

  export covering
  writeAll : FileDesc a => a -> ByteString -> Prog es ()
  writeAll fd (BS 0 _) = pure ()
  writeAll fd bs       =
    injectIO (writeBytes fd bs) >>= \m => writeAll fd (drop (cast m) bs)

  export covering
  writeRawAll : FileDesc a => a -> Bits32 -> Buffer -> Bits32 -> Prog es ()
  writeRawAll fd o buf 0 = pure ()
  writeRawAll fd o buf n =
    injectIO (writeRaw fd buf o n) >>= \w => writeRawAll fd (o+w) buf (n-w)

  export covering
  stream :
       {auto fid : FileDesc a}
    -> (fd : a)
    -> (buffer : Bits32)
    -> (ByteString -> Prog es ())
    -> Prog es ()
  stream fd buf run =
    injectIO (read fd buf) >>= \case
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
        injectIO (readRaw fd buf sz) >>= \case
          0 => pure ()
          n => run buf n >> go buf
