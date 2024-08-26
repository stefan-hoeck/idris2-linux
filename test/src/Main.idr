module Main

import CP
import Data.C.Integer
import Data.Fuel
import File
import Opts
import System
import Tee

%default total

usage : String
usage =
  """
  pack test linux [prog] [args...]
  """

bufferSize : Bits32
bufferSize = 0x10000

end : Fuel
end = limit 1_000_000

parameters {auto has : Has FileErr es}

  readTill : FileDesc a => Fuel -> Nat -> a -> Prog es ()
  readTill Dry      n fd = putStrLn "out of fuel"
  readTill (More x) n fd =
    injectIO (read fd bufferSize) >>= \case
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
    _           => withFile "linux.ipkg" 0 0 (readTill end 0)

covering
main : IO ()
main = runProg $ handleErrors [prettyOut, prettyOut, prettyOut] prog
