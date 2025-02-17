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
inotifyInit : Has Errno es => EIO1 f => InotifyFlags -> f es Inotify
inotifyInit fs = elift1 (P.inotifyInit fs)

||| Watches a file for the given events.
export %inline
inotifyAddWatch : Has Errno es => EIO1 f => Inotify -> String -> InotifyMask -> f es Watch
inotifyAddWatch fd s m = elift1 (P.inotifyAddWatch fd s m)

export %inline
inotifyRm : Has Errno es => EIO1 f => Inotify -> Watch -> f es ()
inotifyRm fd w = elift1 (P.inotifyRm fd w)

||| Reads at most `buf` from an `inotify` file descriptor.
export
inotifyRead : Has Errno es => EIO1 f => (buf : Bits32) -> Inotify -> f es (List InotifyRes)
inotifyRead buf i = elift1 (P.inotifyRead buf i)
