module Example.Util.User

import Data.C.Integer
import Data.List
import public System.Linux.User.Passwd
import public Example.Util.File
import public Example.Util.Prog

%default total

parameters {auto hf : Has Errno es}

  export
  entries : (buf : Bits32) -> Prog es (List PasswdEntry)
  entries buf = do
    bs <- readFile ByteString "/etc/passwd" buf
    pure (mapMaybe readEntry $ unixLines bs)

  export %inline
  getpwnam : String -> Prog es (Maybe PasswdEntry)
  getpwnam name = find ((name ==) . loginName) <$> entries 0x10000

  export %inline
  getuid : String -> Prog es (Maybe UidT)
  getuid name = map uid <$> getpwnam name
