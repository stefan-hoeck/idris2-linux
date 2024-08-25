module Main

import System.Linux.File
import System

%default total

openClose : FilePath -> IO ()
openClose p = do
  Right fd <- openFile p neutral neutral
    | Left err => putStrLn "\{err}"
  putStrLn "Opened \{p} (file desc: \{show fd})"
  ignore $ close fd

main : IO ()
main = do
  openClose "linux.ipkg"
  openClose "linups.ipkg"
