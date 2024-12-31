module IO.Async.Loop.Poller

import IO.Async.Internal.Concurrent
import IO.Async.Internal.Loop
import IO.Async.Internal.Ref

import Data.Array
import Data.C.Ptr

import System.Linux.Eventfd
import System.Linux.Epoll
import System.Posix.Errno.IO
import System.Posix.File
import System.Posix.Limits

%default total

--------------------------------------------------------------------------------
-- Epoll Worker
--------------------------------------------------------------------------------

public export
0 FileHandle : Type
FileHandle = Event -> PrimIO ()

record PollerST where
  constructor PST
  lock     : Mutex
  maxFiles : Nat
  handles  : IOArray maxFiles FileHandle
  events   : CArrayIO maxFiles EpollEvent
  alive    : Ref Alive
  epoll    : Epollfd

getHandle : PollerST -> Bits32 -> PrimIO FileHandle
getHandle s f =
  case tryNatToFin (cast f) of
    Just v  => primRun (get s.handles v)
    Nothing => MkIORes (const primDummy)

setHandle : PollerST -> Bits32 -> FileHandle -> PrimIO ()
setHandle s f fh =
  case tryNatToFin (cast f) of
    Just v  => primRun (set s.handles v fh)
    Nothing => MkIORes ()

%inline
ctl  : PollerST -> EpollOp -> Bits32 -> Event -> PrimIO ()
ctl s op fd (E ev) w =
  let MkIORes _  w := prim__epoll_ctl (fileDesc s.epoll) (opCode op) fd ev w
   in MkIORes () w

removeHandle : PollerST -> Bits32 -> PrimIO ()
removeHandle s b = ctl s Del b 0

handle :
     {auto fd : FileDesc a}
  -> PollerST
  -> (file : a)
  -> Event
  -> FileHandle
  -> PrimIO (PrimIO ())
handle s file ev fh w =
  let fd          := fileDesc file
      MkIORes _ w := setHandle s fd fh w
      MkIORes _ w := ctl s Add fd ev w
   in MkIORes (removeHandle s fd) w

act :
     PollerST
  -> (k : Nat)
  -> {auto 0 p : LTE k n}
  -> CArrayIO n EpollEvent
  -> PrimIO ()
act s 0     arr w = MkIORes () w
act s (S k) arr w =
  let MkIORes ee w := primRun (getNat arr k) w
      MkIORes fd w := prim__get_epoll_event_fd (unwrap ee) w
      MkIORes ev w := prim__get_epoll_event_events (unwrap ee) w
      MkIORes h  w := getHandle s fd w
      MkIORes _  w := h (E ev) w
   in act s k arr w

covering
poll : PollerST -> PrimIO ()
poll s w =
  let MkIORes Run       w := withMutex s.lock (readRef s.alive) w
        | MkIORes _ w => MkIORes () w
      MkIORes (k ** es) w := toPrim (epollWait s.epoll s.events (-1)) w
      MkIORes _         w := act s k es w
   in poll s w

--------------------------------------------------------------------------------
-- Poller
--------------------------------------------------------------------------------

public export
record Poller where
  constructor P
  id : ThreadID
  st : PollerST

||| Stops the `Poller` by setting its `Alive` flag to `Stop`.
export
stop : Poller -> IO ()
stop p = fromPrim $ withMutex p.st.lock $ writeRef p.st.alive Stop

||| Creates an asynchronous scheduler for timed tasks.
|||
||| This sets up a new event loop for processing timed tasks
||| on a single additional thread. The thread will usually wait until
||| either the next scheduled task is due or a new task is submitted
||| via `submit`.
export covering
mkPoller : IO Poller
mkPoller = do
  let mfs := cast {to = Nat} (sysconf SC_OPEN_MAX)
  efd     <- epollCreate 0
  lock    <- fromPrim mkMutex
  alive   <- fromPrim (newRef Run)
  handles <- newIOArray mfs (const primDummy)
  events  <- malloc EpollEvent mfs
  let pst := PST lock mfs handles events alive efd
  id <- fork $ fromPrim $ poll pst
  pure (P id pst)

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

||| Adds a file handle to a `Poller`
export %inline
addHandle :
     {auto fd : FileDesc a}
  -> Poller
  -> (file : a)
  -> Event
  -> FileHandle
  -> PrimIO (PrimIO ())
addHandle = handle . st
