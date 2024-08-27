module File

import Data.Maybe0
import Data.Array.Index
import public Prog
import public System.Linux.File

%default total

tryLT : (m,n : Nat) -> Maybe0 (LT m n)
tryLT m n with (m < n) proof eq
  _ | True  = Just0 (ltOpReflectsLT m n eq)
  _ | False = Nothing0

export
tryClose : FileDesc a => a -> Prog fs ()
tryClose fd = handleError prettyOut (wrapIO $ close fd)

parameters {auto has : Has FileErr es}

  export
  withFile : FilePath -> Flags -> Mode -> (Bits32 -> Prog es a) -> Prog es a
  withFile pth fs m run = do
    fd <- injectIO $ openFile pth fs m
    finally (tryClose fd) (run fd)

  export covering
  writeAll : FileDesc a => a -> ByteString -> Prog es ()
  writeAll fd (BS 0 _) = pure ()
  writeAll fd bs       =
    injectIO (writeBytes fd bs) >>= \case
      WAgain    => writeAll fd bs
      Written m => writeAll fd (drop m bs)

  export covering
  stream :
       {auto fid : FileDesc a}
    -> (fd : a)
    -> (buffer : Bits32)
    -> (ByteString -> Prog es ())
    -> Prog es ()
  stream fd buf run =
    injectIO (read fd buf) >>= \case
      EOF      => pure ()
      Again    => stream fd buf run
      Bytes bs => run bs >> stream fd buf run

  export covering
  copy : FileDesc a => FileDesc b => a -> b -> Prog es ()
  copy i o = stream i 0x10000 (writeAll o)

  export covering
  cp : FilePath -> FilePath -> Prog es ()
  cp i o =
    withFile i 0 0 $ \fi => withFile o create 0o660 $ \fo => copy fi fo
