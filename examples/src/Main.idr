module Main

import Data.C.Integer
import Data.Fuel
import Example.Ch4.Copy
import Example.Ch4.Tee
import Example.Util.File
import Example.Util.Opts
import System
import System.Linux.Process

%default total

usage : String
usage =
  """
  pack test linux [prog] [args...]
  """

end : Fuel
end = limit 1_000_000

parameters {auto has : Has FileErr es}

  readTill : FileDesc a => Fuel -> Nat -> a -> Prog es ()
  readTill Dry      n fd = putStrLn "out of fuel"
  readTill (More x) n fd =
    injectIO (read fd 0x10000) >>= \case
      EOF            => putStrLn "reached end of file after \{show n} bytes"
      Again          => putStrLn "currently no data"
      Bytes (BS m y) => putStrLn "read \{show m} bytes" >> readTill x (m+n) fd

covering
prog : Prog [Error, FileErr, ArgErr] ()
prog = do
  (_::args) <- getArgs | [] => fail (WrongArgs usage)
  case args of
    "copy" :: t => copyProg t
    "tee"  :: t => tee t
    _           => do
      pid  <- getpid
      ppid <- getppid
      putStrLn "Process ID: \{show pid} (parent: \{show ppid})"
      withFile "linux.ipkg" 0 0 (readTill end 0)
      injectIO $ addFlags Stdin O_NONBLOCK
      readTill end 0 Stdin
      withFile "build/out" O_CREAT 0o600 $ \fd => writeAll fd "hello world"

covering
main : IO ()
main = runProg $ handleErrors [prettyOut, prettyOut, prettyOut] prog
