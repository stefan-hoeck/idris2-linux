module Example.Ch19.Inotify

import Data.String

import System.Linux.Inotify

import Example.Util.File
import Example.Util.Opts

%default total

usage : String
usage =
  """
  Usage: linux-examples inotify [PATH]...

  Monitor file events for the given list of files and directories.
  """

lst : InotifyRes -> InotifyMask -> String -> List String
lst res m s = if res.mask `has` m then [s] else []

check : InotifyRes -> List String
check res =
  join
    [ lst res IN_ACCESS "IN_ACCESS"
    , lst res IN_ATTRIB "IN_ATTRIB"
    , lst res IN_CLOSE_NOWRITE "IN_CLOSE_NOWRITE"
    , lst res IN_CLOSE_WRITE "IN_CLOSE_WRITE"
    , lst res IN_CREATE "IN_CREATE"
    , lst res IN_DELETE "IN_DELETE"
    , lst res IN_DELETE_SELF "IN_DELETE_SELF"
    , lst res IN_IGNORED "IN_IGNORED"
    , lst res IN_ISDIR "IN_ISDIR"
    , lst res IN_MODIFY "IN_MODIFY"
    , lst res IN_MOVE_SELF "IN_MOVE_SELF"
    , lst res IN_MOVED_TO "IN_MOVED_TO"
    , lst res IN_MOVED_FROM "IN_MOVED_FROM"
    , lst res IN_OPEN "IN_OPEN"
    , lst res IN_Q_OVERFLOW "IN_Q_OVERFLOW"
    , lst res IN_UNMOUNT "IN_UNMOUNT"
    ]

showRes : InotifyRes -> String
showRes r = "\{r.watch}(\{show r.cookie}): \{unwords $ check r}"

parameters {auto hf : Has Errno es}

  covering
  observe : Inotify -> Prog es ()
  observe fd = do
    rs <- inotifyRead 0x10000 fd
    traverse_ (stdoutLn . showRes) rs
    observe fd

  export covering
  inotify : Has ArgErr es => List String -> Prog es ()
  inotify ["--help"] = stdoutLn usage
  inotify args       = do
    fd <- inotifyInit 0
    _  <- traverse (\s => inotifyAddWatch fd s IN_ALL_EVENTS) args
    observe fd
