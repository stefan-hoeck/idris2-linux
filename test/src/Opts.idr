module Opts

import Data.FilePath
import Derive.Prelude
import System.GetOpts
import public Prog

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Reading command-line options and arguments
--------------------------------------------------------------------------------

public export
data OptTag : Type where
  OPath : OptTag

%runElab derive "OptTag" [Show,Eq,Ord]

export
Interpolation OptTag where
  interpolate OPath = "path"


public export
0 OptType : OptTag -> Type
OptType OPath = FilePath

public export
data ArgErr : Type where
  WrongArgs : (usage : String) -> ArgErr
  Invalid   : (tag : OptTag) -> (str : String) -> ArgErr

%runElab derive "ArgErr" [Show,Eq,Ord]

export
Interpolation ArgErr where
  interpolate (WrongArgs usage) =
    """
    Invalid arguments. Usage:

    \{usage}
    """
  interpolate (Invalid tag str) = "Invalid \{tag}: \"\{str}\""

export
readOpt : (t : OptTag) -> String -> Either ArgErr (OptType t)
readOpt OPath s = maybe (Left $ Invalid OPath s) Right $ parse s

export
readOptIO : Has ArgErr es => (t : OptTag) -> String -> Prog es (OptType t)
readOptIO p = injectEither . readOpt p
