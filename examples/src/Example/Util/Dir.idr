module Example.Util.Dir

import Data.Buffer
import public System.Posix.Dir
import public Example.Util.Prog

%default total

parameters {auto hf : Has Errno es}

  export covering
  withDirSt : String -> s -> (s -> String -> Prog es s) -> Prog es s
  withDirSt pth ini f = puse1 (opendir pth) (flip go ini)

    where
      covering
      go : Dir -> s -> Prog es s
      go dir st = do
        readdir String dir >>= \case
          Res p => f st p >>= go dir
          _     => pure st

  export covering
  withDir : String -> (String -> Prog es ()) -> Prog es ()
  withDir pth = withDirSt pth () . const
