module Main

import Data.Fuel
import System.Linux.File
import System

%default total

bufferSize : Bits32
bufferSize = 0x10000

end : Fuel
end = limit 1_000_000

readTill : FileDesc a => Fuel -> a -> Nat -> IO ()
readTill Dry      fd n = putStrLn "out of fuel"
readTill (More x) fd n =
  read fd bufferSize >>= \case
    EOF       => putStrLn "reached end of file after \{show n} bytes"
    Again     => putStrLn "currently no data"
    Err y     => putStrLn "error reading file: \{y}"
    Bytes m y => do
      putStrLn "read \{show m} bytes"
      readTill x fd (m+n)

tryClose : FileDesc a => a -> IO ()
tryClose fd = do
  Right () <- close fd | Left err => putStrLn "\{err}"
  putStrLn "Closed file desc \{show $ fileDesc fd}"

openClose : FilePath -> IO ()
openClose p = do
  Right fd <- openFile p neutral neutral
    | Left err => putStrLn "\{err}"
  putStrLn "Opened \{p} (file desc: \{show fd})"
  readTill end fd 0
  tryClose fd

main : IO ()
main = do
  openClose "linux.ipkg"
  openClose "linups.ipkg"
  tryClose (the Bits32 100)
  putStrLn "reading from stdin:\n"
  readTill end Stdin 0
