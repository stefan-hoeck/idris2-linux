module Example.Util.Dir

import Data.Buffer
import public System.Posix.Dir
import public Example.Util.Prog

%default total

export %inline
Resource Dir where cleanup d = handleError prettyErrno (closedir d)

parameters {auto hf : Has Errno es}

  export covering
  withDirSt : String -> s -> (s -> String -> Prog es s) -> Prog es s
  withDirSt pth ini f = use1 (opendir pth) (flip go ini)

    where
      covering
      go : Dir -> s -> Prog es s
      go dir st = do
        readdir dir >>= \case
          Nothing   => pure st
          Just p    => f st (toString p) >>= go dir

  export covering
  withDir : String -> (String -> Prog es ()) -> Prog es ()
  withDir pth = withDirSt pth () . const
