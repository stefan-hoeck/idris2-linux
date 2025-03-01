module System.Posix.Poll

import System.Posix.Poll.Prim as P

import public System.Posix.Errno
import public System.Posix.File
import public System.Posix.Poll.Struct
import public System.Posix.Poll.Types

%default total

||| Polls the given array of poll file descriptors for file system events.
export %inline
poll :
     {n : _}
  -> {auto has : Has Errno es}
  -> {auto eio : EIO1 f}
  -> CArrayIO n PollFD
  -> (timeout : Int32)
  -> f es (List PollPair)
poll arr timeout = elift1 (P.poll arr timeout)

||| Polls the given list of poll file pairs for file system events.
export %inline
pollList :
     {auto has : Has Errno es}
  -> {auto eio : EIO1 f}
  -> List PollPair
  -> (timeout : Int32)
  -> f es (List PollPair)
pollList pairs timeout = elift1 (P.pollList pairs timeout)
