module Main

import File
import Data.Fuel
import System

%default total

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

run : Prog [Error, FileErr] () -> IO ()
run = runProg . handleErrors [prettyOut, prettyOut]

covering
main : IO ()
main = do
  run $ withFile "linux.ipkg" 0 0 (readTill end 0)
  run $ withFile "linups.ipkg" 0 0 (readTill end 0)
  run $ tryClose (the Bits32 100)
  run $ cp "linux.ipkg" "out"
  run $ withFile "stdout" (O_WRONLY <+> O_CREAT <+> O_APPEND) 0o600 $ \fo =>
    copy Stdin fo
