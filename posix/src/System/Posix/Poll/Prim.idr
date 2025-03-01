module System.Posix.Poll.Prim

import Data.C.Ptr
import Data.C.Array

import System.Posix.File.Prim

import public System.Posix.Poll.Struct
import public System.Posix.Poll.Types

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C__collect_safe:li_poll, posix-idris"
prim__poll: AnyPtr -> Bits32 -> Int32 -> PrimIO CInt

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Polls the given array of poll file descriptors for file system events.
export
poll :
     {n : _}
  -> CArrayIO n PollFD
  -> (timeout : Int32)
  -> EPrim (List PollPair)
poll arr timeout t =
  let p     := unsafeUnwrap arr
      r # t := ffi (prim__poll p (cast n) timeout) t
   in case r of
        0 => R [] t
        _ => if r < 0
               then E (inject $ fromNeg r) t
               else f1ToE1 (pollResults arr) t

||| Polls the given list of poll file pairs for file system events.
export
pollList : List PollPair -> (timeout : Int32) -> EPrim (List PollPair)
pollList pairs timeout =
  withCArray PollFD (length pairs) $ \arr,t =>
   let _ # t := writeFiles arr pairs t
    in poll arr timeout t
