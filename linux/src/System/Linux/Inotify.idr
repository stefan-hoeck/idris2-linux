module System.Linux.Inotify

import Data.C.Array
import Derive.Prelude
import public System.Linux.Inotify.Flags
import public System.Posix.File

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_inotify_init, linux-idris"
prim__inotify_init1 : Bits32 -> PrimIO CInt

%foreign "C:li_inotify_add_watch, linux-idris"
prim__inotify_add_watch : Bits32 -> String -> Bits32 -> PrimIO CInt

%foreign "C:li_inotify_rm, linux-idris"
prim__inotify_rm : Bits32 -> Bits32 -> PrimIO CInt

%foreign "C:li_inotify_more, linux-idris"
prim__inotify_more : AnyPtr -> AnyPtr -> Bits32 -> Bits32

%foreign "C:li_inotify_next, linux-idris"
prim__inotify_next : AnyPtr -> AnyPtr

%foreign "C:li_inotify_wd, linux-idris"
prim__inotify_wd : AnyPtr -> Bits32

%foreign "C:li_inotify_mask, linux-idris"
prim__inotify_mask : AnyPtr -> Bits32

%foreign "C:li_inotify_cookie, linux-idris"
prim__inotify_cookie : AnyPtr -> Bits32

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

||| An `inotify` file descriptor.
export
record Inotify where
  constructor I
  fd : Bits32

export %inline
Cast Inotify Fd where cast = cast . fd

%runElab derive "Inotify" [Show,Eq,Ord]

||| An `inotify` file descriptor.
export
record Watch where
  constructor W
  wd : Bits32

%runElab derive "Watch" [Show,Eq,Ord]

public export
record InotifyRes where
  constructor IR
  watch  : Watch
  mask   : InotifyEvent
  cookie : Bits32
  name   : String

%runElab derive "InotifyRes" [Show,Eq]

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Opens a new `inotify` file descriptor.
export %inline
inotifyInit : InotifyFlags -> IO (Either Errno Inotify)
inotifyInit (IF f) = toVal (I . cast) $ prim__inotify_init1 f

||| Watches a file for the given events.
export %inline
inotifyAddWatch : Inotify -> String -> InotifyEvent -> IO (Either Errno Watch)
inotifyAddWatch (I f) s (IE e) = toVal (W . cast) $ prim__inotify_add_watch f s e

export %inline
inotifyRm : Inotify -> Watch -> IO (Either Errno ())
inotifyRm (I f) (W w) = toUnit $ prim__inotify_rm f w

reslt : AnyPtr -> InotifyRes
reslt p =
  IR
    { watch  = W $ prim__inotify_wd p
    , mask   = IE $ prim__inotify_mask p
    , cookie = prim__inotify_cookie p
    , name   = ""
    }

results : SnocList InotifyRes -> AnyPtr -> AnyPtr -> Bits32 -> List InotifyRes
results sx orig cur sz =
  case prim__inotify_more orig cur sz of
    0 => sx <>> []
    _ =>
      results
        (sx :< reslt cur)
        orig
        (assert_smaller cur $ prim__inotify_next cur)
        sz

export
inotifyRead : (buf : Bits32) -> Inotify -> IO (Either Errno $ List InotifyRes)
inotifyRead buf i =
  withPtr (cast buf) $ \p => readPtr i p buf >>= \case
    Left x  => pure (Left x)
    Right x => pure (Right $ results [<] p p x)
