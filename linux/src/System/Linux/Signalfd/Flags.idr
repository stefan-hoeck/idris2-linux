-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Linux.Signalfd.Flags

import Data.Bits
import Derive.Prelude

%default total
%language ElabReflection

public export
record SignalfdFlags where
  constructor F
  flags : Bits32

%runElab derive "SignalfdFlags" [Show,Eq,Ord,FromInteger]

public export
Semigroup SignalfdFlags where
  F x <+> F y = F $ x .|. y

public export
Monoid SignalfdFlags where neutral = F 0

public export
SFD_CLOEXEC : SignalfdFlags
SFD_CLOEXEC = 524288

public export
SFD_NONBLOCK : SignalfdFlags
SFD_NONBLOCK = 2048

public export
signalfd_siginfo_size : Nat
signalfd_siginfo_size = 128
