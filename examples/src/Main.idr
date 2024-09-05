module Main

import Data.C.Integer
import Data.Fuel

import Example.Ch4.Copy
import Example.Ch4.CopyWithHoles
import Example.Ch4.Seek
import Example.Ch4.Tee

import Example.Ch5.Seek0Append
import Example.Ch5.AtomicAppend

import Example.Ch12.Processes
import Example.Ch12.HasFileOpen

import Example.Ch19.Inotify

import Example.Ch20.SigSender
import Example.Ch20.SigReceiver

import Example.Util.File
import Example.Util.Opts
import System
import System.Posix.Dir
import System.Posix.File.Stats
import System.Posix.Process

%default total

usage : String
usage =
  """
  Usage: Install with `pack install-app linux-examples` and then run with

         linux-examples [prog] [args]...
  """

end : Fuel
end = limit 1_000_000

parameters {auto has : Has Errno es}

  readTill : FileDesc a => Fuel -> Nat -> a -> Prog es ()
  readTill Dry      n fd = putStrLn "out of fuel"
  readTill (More x) n fd =
    injectIO (read fd 0x10000) >>= \case
      BS 0 _ => putStrLn "reached end of file after \{show n} bytes"
      BS m y => putStrLn "read \{show m} bytes" >> readTill x (m+n) fd

linuxIpkg : String
linuxIpkg = "linux/linux.ipkg"

covering
prog : Prog [Errno, ArgErr] ()
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
    "processes" :: t => processes t
    "has_open" :: t => hasOpen t
    "inotify" :: t => inotify t
    "sig_send" :: t => sigSend t
    "sig_receive" :: t => sigReceive t
    _           => do
      pid  <- getpid
      ppid <- getppid
      putStrLn "Process ID: \{show pid} (parent: \{show ppid})"
      withFile linuxIpkg 0 0 (readTill end 0)
      injectIO $ addFlags Stdin O_NONBLOCK
      (fd,str) <- injectIO (mkstemp "linux/build/hello")
      putStrLn "opened temporary file: \{str}"
      writeAll fd "a temporary hello world\n"
      tryClose fd
      injectIO (statvfs linuxIpkg) >>= printLn
      injectIO (lstat linuxIpkg) >>= printLn
      injectIO (lstat "src") >>= printLn
      injectIO (lstat "/home/gundi/playground/linux.ipkg") >>= printLn
      injectIO (readlink "/home/gundi/playground/linux.ipkg") >>= ignore . injectIO . writeBytes Stdout
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
main = runProg $ handleErrors [prettyOut, prettyOut] prog
