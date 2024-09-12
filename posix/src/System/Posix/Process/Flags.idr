-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Posix.Process.Flags

import Data.Bits
import Data.C.Integer
import Derive.Prelude

%default total
%language ElabReflection

public export
record WaitFlags where
  constructor F
  flags : Bits32

%runElab derive "WaitFlags" [Show,Eq,Ord,FromInteger]

public export
Semigroup WaitFlags where
  F x <+> F y = F $ x .|. y

public export
Monoid WaitFlags where neutral = F 0

public export
data IdType = P_ALL | P_PID | P_PGID

%runElab derive "IdType" [Show,Eq,Ord]


public export
WUNTRACED : WaitFlags
WUNTRACED = 2

public export
WCONTINUED : WaitFlags
WCONTINUED = 8

public export
WNOHANG : WaitFlags
WNOHANG = 1

public export
WEXITED : WaitFlags
WEXITED = 4

public export
WSTOPPED : WaitFlags
WSTOPPED = 2

public export
WNOWAIT : WaitFlags
WNOWAIT = 16777216

public export
idtypeCode : IdType -> Bits8
idtypeCode P_ALL = 0
idtypeCode P_PID = 1
idtypeCode P_PGID = 2
idtypeCode P_PIDFD = 3
