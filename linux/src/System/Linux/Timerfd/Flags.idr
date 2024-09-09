-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Linux.Timerfd.Flags

import Data.Bits
import Derive.Prelude

%default total
%language ElabReflection

public export
record TimerfdFlags where
  constructor F
  flags : Bits32

%runElab derive "TimerfdFlags" [Show,Eq,Ord,FromInteger]

public export
Semigroup TimerfdFlags where
  F x <+> F y = F $ x .|. y

public export
Monoid TimerfdFlags where neutral = F 0

public export
TFD_CLOEXEC : TimerfdFlags
TFD_CLOEXEC = 524288

public export
TFD_NONBLOCK : TimerfdFlags
TFD_NONBLOCK = 2048

public export
TFD_TIMER_ABSTIME : Bits32
TFD_TIMER_ABSTIME = 1
