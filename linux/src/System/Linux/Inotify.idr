module System.Linux.Inotify

import System.Linux.Inotify.Prim as P

import Data.C.Array
import public System.Linux.Inotify.Flags
import public System.Linux.Inotify.Inotify
import public System.Posix.File

%default total

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Opens a new `inotify` file descriptor.
export %inline
inotifyInit : ErrIO io => InotifyFlags -> io Inotify
inotifyInit = eprim . P.inotifyInit

||| Watches a file for the given events.
export %inline
inotifyAddWatch : ErrIO io => Inotify -> String -> InotifyMask -> io Watch
inotifyAddWatch fd s = eprim . P.inotifyAddWatch fd s

export %inline
inotifyRm : ErrIO io => Inotify -> Watch -> io ()
inotifyRm fd = eprim . P.inotifyRm fd

||| Reads at most `buf` from an `inotify` file descriptor.
export
inotifyRead : ErrIO io => (buf : Bits32) -> Inotify -> io (List InotifyRes)
inotifyRead buf = eprim . P.inotifyRead buf
