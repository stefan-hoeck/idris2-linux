module Example.Ch19.Inotify

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

parameters {auto hf : Has Errno es}

  covering
  observe : Inotify -> Prog es ()
  observe fd = do
    rs <- injectIO (inotifyRead 0x10000 fd)
    traverse_ printLn rs
    observe fd

  export covering
  inotify : Has ArgErr es => List String -> Prog es ()
  inotify ["--help"] = putStrLn "\{usage}"
  inotify args       = do
    fd <- injectIO (inotifyInit 0)
    _  <- traverse (\s => injectIO (inotifyAddWatch fd s IN_ALL_EVENTS)) args
    observe fd
  inotify _          = fail (WrongArgs usage)
