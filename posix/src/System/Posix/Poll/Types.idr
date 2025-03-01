-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Posix.Poll.Types

import Data.Bits
import Derive.Prelude

%default total
%language ElabReflection

public export
record PollEvent where
  constructor PE
  event : Bits32

%runElab derive "PollEvent" [Show,Eq,Ord,FromInteger]

public export
Semigroup PollEvent where
  PE x <+> PE y = PE $ x .|. y

public export
Monoid PollEvent where neutral = PE 0

export
hasEvent : PollEvent -> PollEvent -> Bool
hasEvent (PE x) (PE y) = (x .&. y) == y

public export
POLLIN : PollEvent
POLLIN = 1

public export
POLLOUT : PollEvent
POLLOUT = 4

public export
POLLPRI : PollEvent
POLLPRI = 2

public export
POLLERR : PollEvent
POLLERR = 8

public export
POLLHUP : PollEvent
POLLHUP = 16

public export %inline
pollfd_size : Bits32
pollfd_size = 8
