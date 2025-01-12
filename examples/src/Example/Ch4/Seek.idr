module Example.Ch4.Seek

import Example.Util.File
import Example.Util.Opts
import Example.Util.Pretty

%default total

usage : String
usage =
  """
  Usage: linux-examples seek DEST [cmd]...

  Commands:
  s[offset] seek to the given offset
  r[length] read `length` bytes and display them as text
  R[length] read `length` bytes and display them in hexadecimal
  w[str]    write string `str` at the given position
  """

data Cmd : Type where
  Seek    : OffT   -> Cmd
  Read    : Bits32 -> Cmd
  ReadHex : Bits32 -> Cmd
  Write   : String -> Cmd

readCmd : String -> Either ArgErr Cmd
readCmd s =
  case unpack s of
    's' :: t => Seek    <$> readOpt OOff (pack t)
    'r' :: t => Read    <$> readOpt OBits32 (pack t)
    'R' :: t => ReadHex <$> readOpt OBits32 (pack t)
    'w' :: t => Right (Write $ pack t)
    _        => Left $ WrongArgs usage

rd : Bool -> Bits32 -> String
rd False n = "r\{show n}"
rd True  n = "R\{show n}"

disp : Bool -> ByteString -> String
disp False = toString
disp True  = toHexString (Just ':')

parameters {auto hf : Has Errno es}

  readHere : Bool -> Fd -> Bits32 -> Prog es ()
  readHere b fd n = read fd _ n >>= \x => stdoutLn "\{rd b n}: \{disp b x}"

  seek : List Cmd -> (fd : Fd) -> Prog es ()
  seek []        fd = pure ()
  seek (x :: xs) fd = cmd x >> seek xs fd
    where
      cmd : Cmd -> Prog es ()
      cmd (Seek i)    = do
        o <- lseek fd i SEEK_SET
        stdoutLn "s\{show i}: moved to \{show o}"

      cmd (Read m)    = readHere False fd m
      cmd (ReadHex m) = readHere True  fd m

      cmd (Write str) =
        write fd str >>= \n => stdoutLn "s\{str}: wrote \{show n} bytes"

  export
  seekProg : Has ArgErr es => List String -> Prog es ()
  seekProg ["--help"] = stdoutLn usage
  seekProg (i::t) = do
    fi <- readOptIO OPath i
    cs <- injectEither (traverse readCmd t)
    withFile fi (O_RDWR <+> O_CREAT) 0o666 (seek cs)
  seekProg _ = fail (WrongArgs usage)
