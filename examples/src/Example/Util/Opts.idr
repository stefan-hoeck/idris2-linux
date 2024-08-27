module Example.Util.Opts

import Data.ByteString
import Data.FilePath
import Derive.Prelude
import System
import System.GetOpts

import public Data.C.Integer
import public Example.Util.Prog

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Reading command-line options and arguments
--------------------------------------------------------------------------------

public export
data OptTag : Type where
  OPath   : OptTag
  OSize   : OptTag
  OBits32 : OptTag

%runElab derive "OptTag" [Show,Eq,Ord]

export
Interpolation OptTag where
  interpolate OPath   = "path"
  interpolate OSize   = "size"
  interpolate OBits32 = "bits32"


public export
0 OptType : OptTag -> Type
OptType OPath   = FilePath
OptType OSize   = SizeT
OptType OBits32 = Bits32

public export
data ArgErr : Type where
  WrongArgs : (usage : String) -> ArgErr
  Invalid   : (tag : OptTag) -> (str : String) -> ArgErr

%runElab derive "ArgErr" [Show,Eq,Ord]

export
Interpolation ArgErr where
  interpolate (WrongArgs usage) =
    """
    Invalid arguments.

    \{usage}
    """
  interpolate (Invalid tag str) = "Invalid \{tag}: \"\{str}\""

parseNat : Cast Nat t => String -> Either ArgErr t
parseNat s =
  let bs  := fromString {ty = ByteString} s
      res := parseDecimalNat bs <|> parseHexadecimalNat bs
   in maybe (Left $ Invalid OSize s) (Right . cast) res

export
readOpt : (t : OptTag) -> String -> Either ArgErr (OptType t)
readOpt OPath   s = maybe (Left $ Invalid OPath s) Right $ parse s
readOpt OSize   s = parseNat s
readOpt OBits32 s = parseNat s

export
readOptIO : Has ArgErr es => (t : OptTag) -> String -> Prog es (OptType t)
readOptIO p = injectEither . readOpt p

--------------------------------------------------------------------------------
--
--------------------------------------------------------------------------------

export
parseEnv : HasIO io => (t : OptTag) -> String -> Lazy (OptType t) -> io (OptType t)
parseEnv t s v = do
  Just str <- getEnv s | Nothing => pure v
  either (const $ pure v) pure (readOpt t str)
