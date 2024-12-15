-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Linux.Eventfd.Flags

import Data.Bits
import Derive.Prelude

%default total
%language ElabReflection

public export
record EventfdFlags where
  constructor F
  flags : Bits32

%runElab derive "EventfdFlags" [Show,Eq,Ord,FromInteger]

public export
Semigroup EventfdFlags where
  F x <+> F y = F $ x .|. y

public export
Monoid EventfdFlags where neutral = F 0

public export
EFD_CLOEXEC : EventfdFlags
EFD_CLOEXEC = 524288

public export
EFD_NONBLOCK : EventfdFlags
EFD_NONBLOCK = 2048

public export
EFD_SEMAPHORE : EventfdFlags
EFD_SEMAPHORE = 1
