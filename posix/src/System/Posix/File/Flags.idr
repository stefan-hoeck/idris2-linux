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


public export
O_RDONLY : Flags
O_RDONLY = 0

public export
O_WRONLY : Flags
O_WRONLY = 1

public export
O_RDWR : Flags
O_RDWR = 2

public export
O_CLOEXEC : Flags
O_CLOEXEC = 524288

public export
O_CREAT : Flags
O_CREAT = 64

public export
O_DIRECTORY : Flags
O_DIRECTORY = 65536

public export
O_EXCL : Flags
O_EXCL = 128

public export
O_NOCTTY : Flags
O_NOCTTY = 256

public export
O_NOFOLLOW : Flags
O_NOFOLLOW = 131072

public export
O_TRUNC : Flags
O_TRUNC = 512

public export
O_APPEND : Flags
O_APPEND = 1024

public export
O_ASYNC : Flags
O_ASYNC = 8192

public export
O_DSYNC : Flags
O_DSYNC = 4096

public export
O_NONBLOCK : Flags
O_NONBLOCK = 2048

public export
O_SYNC : Flags
O_SYNC = 1052672

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

