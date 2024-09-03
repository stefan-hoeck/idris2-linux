module Example.Util.Dir

import Data.Buffer
import public System.Linux.Dir
import public Example.Util.Prog

%default total

export
tryClose : Dir -> Prog es ()
tryClose d = handleError prettyErr (wrapIO $ closedir d)

parameters {auto hf : Has FileErr es}

  export covering
  withDirSt : FilePath -> s -> (s -> Body -> Prog es s) -> Prog es s
  withDirSt pth ini f = do
    dir <- injectIO (opendir pth)
    finally (tryClose dir) (go dir ini)

    where
      covering
      go : Dir -> s -> Prog es s
      go dir st = do
        injectIO (readdir dir) >>= \case
          Nothing   => pure st
          Just p    => do
            let str := toString p
            case Body.parse (toString p) of
              Just b  => f st b >>= go dir
              Nothing => go dir st

  export covering
  withDir : FilePath -> (Body -> Prog es ()) -> Prog es ()
  withDir pth = withDirSt pth () . const
