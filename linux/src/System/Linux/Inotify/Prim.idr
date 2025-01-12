module System.Linux.Inotify.Prim

import Data.C.Array
import public System.Linux.Inotify.Flags
import public System.Linux.Inotify.Inotify
import public System.Posix.File.Prim

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_inotify_init1, linux-idris"
prim__inotify_init1 : Bits32 -> PrimIO CInt

%foreign "C:li_inotify_add_watch, linux-idris"
prim__inotify_add_watch : Bits32 -> String -> Bits32 -> PrimIO CInt

%foreign "C:li_inotify_rm, linux-idris"
prim__inotify_rm : Bits32 -> Bits32 -> PrimIO CInt

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Opens a new `inotify` file descriptor.
export %inline
inotifyInit : InotifyFlags -> EPrim Inotify
inotifyInit (IF f) = toVal cast $ prim__inotify_init1 f

||| Watches a file for the given events.
export %inline
inotifyAddWatch : Inotify -> String -> InotifyMask -> EPrim Watch
inotifyAddWatch f s (IM m) =
  toVal cast $ prim__inotify_add_watch (fileDesc f) s m

export %inline
inotifyRm : Inotify -> Watch -> EPrim ()
inotifyRm f w = toUnit $ prim__inotify_rm (fileDesc f) (cast w)

||| Reads at most `buf` from an `inotify` file descriptor.
export %inline
inotifyRead : (buf : Bits32) -> Inotify -> EPrim (List InotifyRes)
inotifyRead buf i = read i _ buf
