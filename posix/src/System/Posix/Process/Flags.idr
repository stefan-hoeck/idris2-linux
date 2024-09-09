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
  flags : CInt

%runElab derive "WaitFlags" [Show,Eq,Ord,FromInteger]

public export
Semigroup WaitFlags where
  F x <+> F y = F $ x .|. y

public export
Monoid WaitFlags where neutral = F 0


public export
WUNTRACED : WaitFlags
WUNTRACED = 2

public export
WCONTINUED : WaitFlags
WCONTINUED = 8

public export
WNOHANG : WaitFlags
WNOHANG = 1
