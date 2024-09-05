-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Posix.Signal.Types

import Data.Bits
import Data.C.Integer
import Derive.Prelude

%default total
%language ElabReflection

public export
data How : Type where
  SIG_BLOCK   : How
  SIG_UNBLOCK : How
  SIG_SETMASK : How

%runElab derive "How" [Show,Eq,Ord]

public export
record SignalFlags where
  constructor F
  flags : Bits64

%runElab derive "SignalFlags" [Show,Eq,Ord,FromInteger]

public export %inline
Semigroup SignalFlags where
  F x <+> F y = F $ x .|. y

public export %inline
Monoid SignalFlags where neutral = F 0

public export
howCode : How -> Bits8
howCode SIG_BLOCK   = 0
howCode SIG_UNBLOCK = 1
howCode SIG_SETMASK = 2

public export
SA_NOCLDSTOP : SignalFlags
SA_NOCLDSTOP = 1

public export
SA_NOCLDWAIT : SignalFlags
SA_NOCLDWAIT = 2

public export
SA_NODEFER : SignalFlags
SA_NODEFER = 1073741824

public export
SA_ONSTACK : SignalFlags
SA_ONSTACK = 134217728

public export
SA_RESETHAND : SignalFlags
SA_RESETHAND = 2147483648

public export
SA_RESTART : SignalFlags
SA_RESTART = 268435456

public export
SA_SIGINFO : SignalFlags
SA_SIGINFO = 4
