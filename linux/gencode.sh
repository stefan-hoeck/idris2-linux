#!/usr/bin/env bash

make -C codegen all
make -C support all

cat >src/System/Linux/Inotify/Flags.idr <<EOT
-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Linux.Inotify.Flags

import Data.Bits
import Derive.Prelude

%default total
%language ElabReflection

public export
record InotifyFlags where
  constructor IF
  flags : Bits32

%runElab derive "InotifyFlags" [Show,Eq,Ord,FromInteger]

public export
Semigroup InotifyFlags where
  IF x <+> IF y = IF $ x .|. y

public export
Monoid InotifyFlags where neutral = IF 0

public export
record InotifyMask where
  constructor IM
  mask : Bits32

namespace InotifyMask
  %runElab derive "InotifyMask" [Show,Eq,Ord,FromInteger]

public export
Semigroup InotifyMask where
  IM x <+> IM y = IM $ x .|. y

public export
Monoid InotifyMask where neutral = IM 0

||| Checks if an inotify event mask holds the given event.
export
has : InotifyMask -> InotifyMask -> Bool
has (IM x) (IM y) = y == (x .&. y)

EOT

codegen/inotify_gen >>src/System/Linux/Inotify/Flags.idr

cat >src/System/Linux/Signalfd/Flags.idr <<EOT
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
EOT

codegen/signalfd_gen >>src/System/Linux/Signalfd/Flags.idr

cat >src/System/Linux/Timerfd/Flags.idr <<EOT
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
EOT

codegen/timerfd_gen >>src/System/Linux/Timerfd/Flags.idr

cat >src/System/Linux/Eventfd/Flags.idr <<EOT
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
EOT

codegen/eventfd_gen >>src/System/Linux/Eventfd/Flags.idr
