module Main

import Data.C.Integer
import Data.Fuel
import Data.IORef

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

import Example.Ch22.SigReceiverFd

import Example.Ch23.TimerExample
import Example.Ch23.TimerfdExample

import Example.Ch24.ForkExample

import Example.Ch27.ExecveExample
import Example.Ch27.ExecveHello
import Example.Ch27.SystemExample

import Example.Ch44.BasicPipe
import Example.Ch44.ChunkPipe
import Example.Ch44.PipeSync
import Example.Ch44.FifoServer

import Example.Ch57.DgramClient
import Example.Ch57.DgramServer
import Example.Ch57.UnixClient
import Example.Ch57.UnixServer

import Example.Ch63.EpollExample
import Example.Ch63.EpollPerformance

import Example.Util.File
import Example.Util.Opts
import Example.Util.Pthreads
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
  readTill Dry      n fd = stdoutLn "out of fuel"
  readTill (More x) n fd =
    read fd ByteString 0x10000 >>= \case
      BS 0 _ => stdoutLn "reached end of file after \{show n} bytes"
      BS m y => stdoutLn "read \{show m} bytes" >> readTill x (m+n) fd

linuxIpkg : String
linuxIpkg = "linux/linux.ipkg"

covering
loop : IORef Nat -> Nat -> Prog [Errno] ()
loop ref (S k) = modifyIORef ref S >> loop ref k
loop ref 0     = do
  pthreadTestCancel
  modifyIORef ref S
  loop ref 1000

covering
other : IORef Nat -> IORef PthreadT -> MutexT -> CondT -> IO ()
other cnt ref mu co =
  runProg $ handleErrors [prettyOut] $ do
    tid <- pthreadSelf
    stdoutLn "New thread's ID: \{show tid}"
    lockMutex mu
    writeIORef ref tid
    unlockMutex mu
    stdoutLn "Signalling waiting main thread."
    ignore $ condSignal co
    loop cnt 1000

covering
prog : Prog [Errno, ArgErr] ()
prog = do
  (_::args) <- getArgs | [] => fail (WrongArgs usage)
  case args of
    ["--help"]                     => stdoutLn usage
    "copy"                    :: t => copyProg t
    "copyh"                   :: t => copyh t
    "tee"                     :: t => tee t
    "seek"                    :: t => seekProg t
    "atomic_append"           :: t => atomicProg t
    "seek0_append"            :: t => seekAppendProg t
    "processes"               :: t => processes t
    "has_open"                :: t => hasOpen t
    "inotify"                 :: t => inotify t
    "sig_send"                :: t => sigSend t
    "sig_receive"             :: t => sigReceive t
    "sig_receive_fd"          :: t => sigReceiveFd t
    "timer_example"           :: t => timerExample t
    "timerfd_example"         :: t => timerfdExample t
    "fork_example"            :: t => forkExample t
    "execve_example"          :: t => execveExample t
    "execve_hello"            :: t => execveHello t
    "system_example"          :: t => systemExample t
    "basic_pipe"              :: t => basicPipe t
    "chunk_pipe"              :: t => chunkPipe t
    "pipe_sync"               :: t => pipeSync t
    "fifo_server"             :: t => fifoServer t
    "fifo_client"             :: t => fifoClient t
    "unix-client"             :: t => unixClient t
    "unix-server"             :: t => unixServer t
    "dgram-client"            :: t => dgramClient t
    "dgram-server"            :: t => dgramServer t
    "epoll_example"           :: t => epollExample t
    "epoll_performance"       :: t => epollPerformance t
    _                              =>
      use [mkmutex MUTEX_NORMAL, mkcond] $ \[mu,co] => do
        pid  <- getpid
        ppid <- getppid
        stdoutLn "Process ID: \{show pid} (parent: \{show ppid})"
        withFile linuxIpkg 0 0 (readTill end 0)
        addFlags Stdin O_NONBLOCK
        (fd,str) <- mkstemp "linux/build/hello"
        stdoutLn "opened temporary file: \{str}"
        fwrite fd "a temporary hello world\n"
        anyErr $ cleanup fd
        tid <- pthreadSelf
        cnt <- newIORef Z
        ref <- newIORef tid
        lockMutex mu
        stdoutLn "My thread ID: \{show tid}"
        _   <- liftIO (fork $ other cnt ref mu co)
        stdoutLn "Forked child. Awaiting its signal."
        condWait co mu
        oid <- readIORef ref
        stdoutLn "Forked thread with ID: \{show oid}"
        stdoutLn "Eq of my thread ID: \{show $ tid == tid}"
        stdoutLn "Eq with other thread ID: \{show $ oid == tid}"
        stdoutLn "Now canceling child."
        pthreadCancel oid
        res <- pthreadJoin oid
        tot <- readIORef cnt
        stdoutLn "Final count: \{show tot}"
        stdoutLn "Joining result: \{show res}"

covering
main : IO ()
main = do
  runProg $ handleErrors [prettyOut, prettyOut] prog
  exitSuccess
