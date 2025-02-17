module Example.Ch12.Processes

import Data.List
import Data.List1
import Data.String
import Data.SortedMap
import Example.Util.Dir
import Example.Util.File
import Example.Util.Opts
import Example.Util.User

%default total

usage : String
usage =
  """
  Usage: linux-examples processes USER

  Lists the name and process ID of all processes being
  currently run by `USER`
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

toEOF : Errno -> ByteString
toEOF = const ""

parameters {auto hf : Has Errno es}

  inDir : UidT -> String -> Prog es ()
  inDir u p = do
    r <- dropErr toEOF (readFile _ "/proc/\{p}/status" 0x10000)
    let m := processInfo r
    case (lookup "Name" m, hasUID u m) of
      (Just n,True) => stdoutLn "\{p}: \{n}"
      _             => pure ()

  export covering
  processes : Has ArgErr es => List String -> Prog es ()
  processes ["--help"] = stdoutLn usage
  processes [u]        = do
    Just uid <- getuid u | Nothing => throw (Invalid OUser u)
    withDir "/proc" (inDir uid)
  processes _          = throw (WrongArgs usage)
