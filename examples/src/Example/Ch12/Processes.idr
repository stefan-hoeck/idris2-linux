module Example.Ch12.Processes

import Data.List
import Data.List1
import Data.SortedMap
import Example.Util.Dir
import Example.Util.File
import Example.Util.Opts

%default total

usage : String
usage =
  """
  Usage: linux-examples processes USER

  Lists the name of all processes being currently run by `USER`
  """

processInfo : ByteString -> SortedMap String String
processInfo bs = SortedMap.fromList pairs
  where
    line : ByteString -> Maybe (String,String)
    line bs =
      case split 58 bs of
        [x,y] => Just (toString x, trim $ toString y)
        _     => Nothing

    pairs : List (String,String)
    pairs = mapMaybe line (unixLines bs)

hasUID : UidT -> SortedMap String String -> Bool
hasUID n m =
  case lookup "Uid" m of
    Nothing => False
    Just s  => case List.filter (/= "") $ words s of
      h::_ => cast h == n
      []   => False

parameters {auto hf : Has FileErr es}

  inDir : UidT -> FilePath -> Prog es ()
  inDir u p = do
    res <- logAndDropErr {e = FileErr} (($> EOF) . prettyErr) $
      withFile (p /> "status") O_RDONLY 0 $ \fd => do
        injectIO {es} (read fd 0x10000)
    case res of
      EOF     => pure ()
      RAgain  => pure ()
      Bytes x =>
        let m := processInfo x
         in case (lookup "Name" m, hasUID u m) of
              (Just n,True) => liftIO (ignore $ writeStrLn Stdout "\{p}: \{n}")
              _             => pure ()

  export covering
  processes : Has ArgErr es => List String -> Prog es ()
  processes ["--help"] = putStrLn "\{usage}"
  processes [u]        = withDir "/proc" (inDir $ cast u)
  processes _          = fail (WrongArgs usage)
