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

public export
S_IRWXU : Mode
S_IRWXU = 448

public export
S_IRUSR : Mode
S_IRUSR = 256

public export
S_IWUSR : Mode
S_IWUSR = 128

public export
S_IXUSR : Mode
S_IXUSR = 64

public export
S_IRWXG : Mode
S_IRWXG = 56

public export
S_IRGRP : Mode
S_IRGRP = 32

public export
S_IWGRP : Mode
S_IWGRP = 16

public export
S_IXGRP : Mode
S_IXGRP = 8

public export
S_IRWXO : Mode
S_IRWXO = 7

public export
S_IROTH : Mode
S_IROTH = 4

public export
S_IWOTH : Mode
S_IWOTH = 2

public export
S_IXOTH : Mode
S_IXOTH = 1

public export
S_ISUID : Mode
S_ISUID = 2048

public export
S_ISGID : Mode
S_ISGID = 1024

public export
S_ISVTX : Mode
S_ISVTX = 512

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

