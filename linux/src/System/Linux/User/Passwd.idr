module System.Linux.User.Passwd

import Data.C.Integer
import Data.FilePath
import Derive.Prelude

import System.Linux.File

%default total
%language ElabReflection

||| An entry in the `/etc/passwd` file.
public export
record PasswdEntry where
  constructor PE
  loginName : String
  password  : String
  uid       : UidT
  gid       : GidT
  comment   : String
  homedir   : FilePath
  shell     : Maybe FilePath

%runElab derive "PasswdEntry" [Show,Eq]

toShell : String -> Maybe FilePath
toShell "" = Nothing
toShell s  = Just $ fromString s

export
readEntry : ByteString -> Maybe PasswdEntry
readEntry bs =
  case split 58 bs of
    [n,p,u,g,c,h,s] =>
      Just $ PE
        { loginName = toString n
        , password  = toString p
        , uid       = maybe 0 cast $ parseInteger u
        , gid       = maybe 0 cast $ parseInteger g
        , comment   = toString c
        , homedir   = fromString (toString h)
        , shell     = toShell (toString s)
        }
    _               => Nothing
