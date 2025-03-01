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

public export
record Errno where
  constructor EN
  errno : Bits32

%runElab derive "Errno" [Show,Eq,Ord,FromInteger]

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
%hide Language.Reflection.TTImp.Mode

public export
record Flags where
  constructor F
  flags : Bits32

%runElab derive "Flags" [Show,Eq,Ord,FromInteger]

public export
Semigroup Flags where
  F x <+> F y = F $ x .|. y

public export
Monoid Flags where neutral = F 0

||| File permissions.
public export
record Mode where
  constructor M
  mode : ModeT

namespace Mode
  %runElab derive "Mode" [Show,Eq,Ord,FromInteger]

public export
Semigroup Mode where
  M x <+> M y = M $ x .|. y

public export
Monoid Mode where neutral = M 0

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

cat >src/System/Posix/Pthreads/Types.idr <<EOT
-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Posix.Pthreads.Types

import Data.C.Integer
import Derive.Finite
import Derive.Prelude

%default total
%language ElabReflection

public export
data MutexType : Type where
  MUTEX_NORMAL     : MutexType
  MUTEX_RECURSIVE  : MutexType
  MUTEX_ERRORCHECK : MutexType

%runElab derive "MutexType" [Show,Eq,Ord,Finite]

public export
data CancelType : Type where
  CANCEL_DEFERRED     : CancelType
  CANCEL_ASYNCHRONOUS : CancelType

%runElab derive "CancelType" [Show,Eq,Ord,Finite]

public export
data CancelState : Type where
  CANCEL_ENABLE  : CancelState
  CANCEL_DISABLE : CancelState

%runElab derive "CancelState" [Show,Eq,Ord,Finite]

EOT

codegen/pthreads_gen >>src/System/Posix/Pthreads/Types.idr

cat >src/System/Posix/Socket/Types.idr <<EOT
-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Posix.Socket.Types

import Data.Bits
import Data.C.Integer
import Derive.Finite
import Derive.Prelude

%default total
%language ElabReflection

public export
data Domain : Type where
  AF_UNIX  : Domain
  AF_INET  : Domain
  AF_INET6 : Domain

%runElab derive "Domain" [Show,Eq,Ord,Finite]

public export
record SockType where
  constructor ST
  type : Bits32

%runElab derive "SockType" [Show,Eq,Ord,FromInteger]

public export
Semigroup SockType where
  ST x <+> ST y = ST $ x .|. y

public export
record SockFlags where
  constructor SF
  flags : Bits32

namespace SockFlags
  %runElab derive "SockFlags" [Show,Eq,Ord,FromInteger]

public export
Semigroup SockFlags where
  SF x <+> SF y = SF $ x .|. y
EOT

codegen/socket_gen >>src/System/Posix/Socket/Types.idr

cat >src/System/Posix/Poll/Types.idr <<EOT
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
EOT

codegen/poll_gen >>src/System/Posix/Poll/Types.idr
