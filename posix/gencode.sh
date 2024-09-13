#!/usr/bin/env bash

make -C codegen all
make -C support all

cat >src/System/Posix/Errno/Type.idr <<EOT
-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Posix.Errno.Type

import Derive.Finite
import Derive.Prelude

%default total
%language ElabReflection

EOT

codegen/error_gen >>src/System/Posix/Errno/Type.idr

cat >src/System/Posix/File/Flags.idr <<EOT
-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Posix.File.Flags

import Data.Bits
import Data.C.Integer
import Derive.Prelude

%default total
%language ElabReflection

public export
record Flags where
  constructor F
  flags : CInt

%runElab derive "Flags" [Show,Eq,Ord,FromInteger]

public export
Semigroup Flags where
  F x <+> F y = F $ x .|. y

public export
Monoid Flags where neutral = F 0

EOT

codegen/flags_gen >>src/System/Posix/File/Flags.idr

cat >>src/System/Posix/File/Flags.idr <<EOT

||| Flags for creating a file for output.
export
create : Flags
create = O_WRONLY <+> O_CREAT <+> O_TRUNC

||| Flags for creating a file for output.
|||
||| If the file exists, data is appended to it.
export
append : Flags
append = O_WRONLY <+> O_CREAT <+> O_APPEND

EOT

cat >src/System/Posix/File/Whence.idr <<EOT
-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Posix.File.Whence

import Data.C.Integer
import Derive.Finite
import Derive.Prelude

%default total
%language ElabReflection

public export
data Whence = SEEK_SET | SEEK_CUR | SEEK_END

%runElab derive "Whence" [Show,Eq,Ord,Finite]

export
whenceCode : Whence -> Bits8
EOT

codegen/whence_gen >>src/System/Posix/File/Whence.idr

cat >src/System/Posix/Limits.idr <<EOT
-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Posix.Limits

import Data.C.Integer

%default total

export %foreign "C:sysconf, posix-idris"
sysconf : Bits32 -> Long

export %foreign "C:pathconf, posix-idris"
pathconf : String -> Bits32 -> Long

export %foreign "C:fpathconf, posix-idris"
fpathconf : Bits32 -> Bits32 -> Long
EOT

codegen/limits_gen >>src/System/Posix/Limits.idr

cat >src/System/Posix/File/Type.idr <<EOT
-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Posix.File.Type

import Data.Bits
import Data.C.Integer
import Derive.Finite
import Derive.Prelude

%default total
%language ElabReflection

public export
data FileType : Type where
  Regular     : FileType
  Directory   : FileType
  CharDevice  : FileType
  BlockDevice : FileType
  Pipe        : FileType
  Socket      : FileType
  Link        : FileType
  Other       : FileType

%runElab derive "FileType" [Show,Eq,Ord,Finite]

public export
fromMode : ModeT -> FileType
EOT

codegen/filetype_gen >>src/System/Posix/File/Type.idr

cat >src/System/Posix/Signal/Types.idr <<EOT
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
import Data.SortedMap
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
record Signal where
  constructor S
  sig : Bits32

%runElab derive "Signal" [Show,Eq,Ord,FromInteger]

EOT

codegen/signal_gen >>src/System/Posix/Signal/Types.idr

cat >src/System/Posix/Timer/Types.idr <<EOT
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
data ClockId : Type where
  CLOCK_REALTIME           : ClockId
  CLOCK_MONOTONIC          : ClockId
  CLOCK_PROCESS_CPUTIME_ID : ClockId
  CLOCK_THREAD_CPUTIME_ID  : ClockId

%runElab derive "ClockId" [Show,Eq,Ord,Finite]

EOT

codegen/timer_gen >>src/System/Posix/Timer/Types.idr

cat >src/System/Posix/Time/Types.idr <<EOT
-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Posix.Time.Types

import Data.C.Integer

%default total

EOT

codegen/time_gen >>src/System/Posix/Time/Types.idr

cat >src/System/Posix/Process/Flags.idr <<EOT
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

EOT

codegen/process_gen >>src/System/Posix/Process/Flags.idr
