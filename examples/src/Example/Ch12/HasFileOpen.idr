module Example.Ch12.HasFileOpen

import Example.Util.Dir
import Example.Util.File
import Example.Util.Opts

%default total

usage : String
usage =
  """
  Usage: linux-examples has_open PATH

  Lists the process number of the process that has file `PATH`
  currently open.
  """

toEOF : Errno -> ()
toEOF = const ()

parameters {auto hf : Has Errno es}

  srch : ByteString -> String -> String -> Prog es ()
  srch bs p f =
    let pth := "/proc/\{p}/fd/\{f}"
     in dropErr toEOF $ do
          x <- readlink pth
          when (x == bs) (stdoutLn "\{p}")

  covering
  inProc : ByteString -> String -> Prog es ()
  inProc fd p = dropErr toEOF (withDir "/proc/\{p}/fd" (srch fd p))

  export covering
  hasOpen : Has ArgErr es => List String -> Prog es ()
  hasOpen ["--help"] = stdoutLn usage
  hasOpen [p]        = withDir "/proc" (inProc $ fromString p)
  hasOpen _          = throw (WrongArgs usage)
