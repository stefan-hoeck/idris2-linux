module IO.Async.Loop.Poller

import IO.Async.Internal.Concurrent
import IO.Async.Internal.Loop
import IO.Async.Internal.Ref

import Data.Array
import Data.C.Ptr

import System.Linux.Eventfd
import System.Linux.Eventfd.Prim
import System.Linux.Epoll.Prim
import System.Linux.Epoll as E
import System.Posix.File.Prim
import System.Posix.Errno.IO
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
  events   : CArrayIO maxFiles SEpollEvent
  alive    : Ref Alive
  epoll    : Epollfd
  event    : Eventfd
  queue    : Ref (SnocList $ PrimIO ())

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

prim : EPrim a -> PrimIO ()
prim act w =
  case act w of
    R _ w => MkIORes () w
    E x w => stderrLn "Error: \{errorText x} (\{errorName x})" w

%inline
ctl  : PollerST -> EpollOp -> Bits32 -> Event -> PrimIO ()
ctl s op fd ev = prim $ epollCtl s.epoll op fd ev

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

act : PollerST -> List EpollEvent -> PrimIO ()
act s []             w = MkIORes () w
act s (E ev fd :: t) w =
  let MkIORes h  w := getHandle s fd.fd w
      MkIORes _  w := h ev w
   in act s t w

state : PollerST -> PrimIO (Alive, List (PrimIO ()))
state s =
  withMutex s.lock $ \w =>
    let MkIORes al w := readRef s.alive w
        MkIORes sa w := readRef s.queue w
        MkIORes _  w := writeRef s.queue [<] w
     in MkIORes (al, sa <>> []) w

runAll : List (PrimIO ()) -> PrimIO ()
runAll []        w = MkIORes () w
runAll (x :: xs) w =
  let MkIORes _ w := x w
   in runAll xs w

covering
poll : PollerST -> PrimIO ()
poll s w =
  let MkIORes (Run,as) w := state s w | MkIORes _ w => MkIORes () w
      R es w := epollWaitVals s.epoll s.events (-1) w | E x w => poll s w
      MkIORes _        w := act s es w
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
stop p = do
  fromPrim $ withMutex p.st.lock $ writeRef p.st.alive Stop
  writeEventfd p.st.event 1

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
  queue   <- fromPrim (newRef [<])
  handles <- newIOArray mfs (const primDummy)
  events  <- malloc SEpollEvent mfs
  event   <- eventfd 0 0
  let pst := PST lock mfs handles events alive efd event queue
  primIO $ setHandle pst (fileDesc event) (\_ => prim $ Prim.readEventfd event)
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
