-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Posix.Timer.Types

import Data.Bits
import Data.C.Integer
import Derive.Finite
import Derive.Prelude

%default total
%language ElabReflection

public export
data Which = ITIMER_REAL | ITIMER_VIRTUAL | ITIMER_PROF

%runElab derive "Which" [Show,Eq,Ord,Finite]


public export
whichCode : Which -> Bits8
whichCode ITIMER_REAL = 0
whichCode ITIMER_VIRTUAL = 1
whichCode ITIMER_PROF = 2

public export %inline
timeval_size : SizeT
timeval_size = 16

public export %inline
itimerval_size : SizeT
itimerval_size = 32

public export %inline
CLOCKS_PER_SEC : ClockT
CLOCKS_PER_SEC = 1000000