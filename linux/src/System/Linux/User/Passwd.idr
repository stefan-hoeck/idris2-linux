module System.Linux.User.Passwd

import Data.C.Integer
import Derive.Prelude

import System.Posix.File

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
  homedir   : String
  shell     : String

%runElab derive "PasswdEntry" [Show,Eq]

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
        , homedir   = toString h
        , shell     = toString s
        }
    _               => Nothing
