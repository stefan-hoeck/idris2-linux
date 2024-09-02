module Main

import Data.C.Integer
import Data.Fuel

import Example.Ch4.Copy
import Example.Ch4.CopyWithHoles
import Example.Ch4.Seek
import Example.Ch4.Tee

import Example.Ch5.Seek0Append
import Example.Ch5.AtomicAppend

import Example.Util.File
import Example.Util.Opts
import System
import System.Linux.Dir
import System.Linux.File.Stats
import System.Linux.Process

%default total

usage : String
usage =
  """
  Usage: Install with `pack install-app linux-examples` and then run with

         linux-examples [prog] [args]...
  """

end : Fuel
end = limit 1_000_000

parameters {auto has : Has FileErr es}

  readTill : FileDesc a => Fuel -> Nat -> a -> Prog es ()
  readTill Dry      n fd = putStrLn "out of fuel"
  readTill (More x) n fd =
    injectIO (read fd 0x10000) >>= \case
      EOF            => putStrLn "reached end of file after \{show n} bytes"
      RAgain         => putStrLn "currently no data"
      Bytes (BS m y) => putStrLn "read \{show m} bytes" >> readTill x (m+n) fd

covering
prog : Prog [Error, FileErr, ArgErr] ()
prog = do
  (_::args) <- getArgs | [] => fail (WrongArgs usage)
  case args of
    ["--help"]   => putStrLn usage
    "copy"   :: t => copyProg t
    "copyh"  :: t => copyh t
    "tee"    :: t => tee t
    "seek"   :: t => seekProg t
    "atomic_append" :: t => atomicProg t
    "seek0_append" :: t => seekAppendProg t
    _           => do
      pid  <- getpid
      ppid <- getppid
      putStrLn "Process ID: \{show pid} (parent: \{show ppid})"
      withFile "linux.ipkg" 0 0 (readTill end 0)
      injectIO $ addFlags Stdin O_NONBLOCK
      (fd,str) <- injectIO (mkstemp "build/hello")
      putStrLn "opened temporary file: \{str}"
      writeAll fd "a temporary hello world\n"
      tryClose fd
      injectIO (statvfs "linux.ipkg") >>= printLn
      injectIO (lstat "linux.ipkg") >>= printLn
      injectIO (lstat "src") >>= printLn
      injectIO (lstat "/home/gundi/playground/linux.ipkg") >>= printLn
      injectIO (readlink "/home/gundi/playground/linux.ipkg") >>= ignore . injectIO . writeBytes Stdout
      injectIO (mkpdir "/home/gundi/playground/foo/bar/baz/quux" 0o700)
      putStrLn ""
      readTill end 0 Stdin
      injectIO getcwd >>= ignore . injectIO . writeBytes Stdout
      putStrLn ""
      injectIO (chdir "..")
      injectIO getcwd >>= ignore . injectIO . writeBytes Stdout
      putStrLn ""
      injectIO (chroot "/etc")

covering
main : IO ()
main = runProg $ handleErrors [prettyOut, prettyOut, prettyOut] prog
