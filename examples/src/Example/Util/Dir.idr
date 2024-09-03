module Example.Util.Dir

import Data.Buffer
import public System.Posix.Dir
import public Example.Util.Prog

%default total

export
tryClose : Dir -> Prog es ()
tryClose d = handleError prettyErr (wrapIO $ closedir d)

parameters {auto hf : Has Errno es}

  export covering
  withDirSt : String -> s -> (s -> String -> Prog es s) -> Prog es s
  withDirSt pth ini f = do
    dir <- injectIO (opendir pth)
    finally (tryClose dir) (go dir ini)

    where
      covering
      go : Dir -> s -> Prog es s
      go dir st = do
        injectIO (readdir dir) >>= \case
          Nothing   => pure st
          Just p    => f st (toString p) >>= go dir

  export covering
  withDir : String -> (String -> Prog es ()) -> Prog es ()
  withDir pth = withDirSt pth () . const
