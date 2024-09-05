module Example.Util.Opts

import Data.ByteString
import Derive.Prelude
import System
import System.GetOpts
import System.Signal

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
  ONat    : OptTag
  OOff    : OptTag
  OUser   : OptTag
  OPid    : OptTag
  OSig    : OptTag

%runElab derive "OptTag" [Show,Eq,Ord]

export
Interpolation OptTag where
  interpolate OPath   = "path"
  interpolate OSize   = "size"
  interpolate OBits32 = "bits32"
  interpolate ONat    = "nat"
  interpolate OOff    = "offset"
  interpolate OUser   = "user"
  interpolate OPid    = "pid"
  interpolate OSig    = "signal"


public export
0 OptType : OptTag -> Type
OptType OPath   = String
OptType OSize   = SizeT
OptType OOff    = OffT
OptType OBits32 = Bits32
OptType ONat    = Nat
OptType OUser   = String
OptType OPid    = PidT
OptType OSig    = Signal

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

parameters (t      : OptTag)
           {auto c : Cast Integer (OptType t)}
           (s      : String)

  parseNat : Either ArgErr (OptType t)
  parseNat =
    let bs  := fromString {ty = ByteString} s
        res := parseDecimalNat bs
     in maybe (Left $ Invalid t s) (Right . cast @{c} . cast) res

  parseInt : Either ArgErr (OptType t)
  parseInt =
    let bs  := fromString {ty = ByteString} s
        res := parseInteger bs
     in maybe (Left $ Invalid t s) (Right . cast) res

parseSignal : String -> Either ArgErr Signal
parseSignal "SIGUSR1" = Right (SigPosix SigUser1)
parseSignal "SIGUSR2" = Right (SigPosix SigUser2)
parseSignal "SIGHUP"  = Right (SigPosix SigHUP)
parseSignal "SIGTRAP" = Right (SigPosix SigTRAP)
parseSignal "SIGQUIT" = Right (SigPosix SigQUIT)
parseSignal "SIGINT"  = Right SigINT
parseSignal "SIGILL"  = Right SigILL
parseSignal "SIGFPE"  = Right SigFPE
parseSignal "SIGABRT" = Right SigABRT
parseSignal "SIGSEGV" = Right SigSEGV
parseSignal s         = maybe (Left $ Invalid OSig s) Right (toSignal $ cast s)

export
readOpt : (t : OptTag) -> String -> Either ArgErr (OptType t)
readOpt OPath   s = pure s
readOpt OSize   s = parseNat OSize s
readOpt OBits32 s = parseNat OBits32 s
readOpt OOff    s = parseInt OOff s
readOpt ONat    s = parseNat ONat s
readOpt OUser   s = pure s
readOpt OPid    s = parseNat OPid s
readOpt OSig    s = parseSignal s

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
