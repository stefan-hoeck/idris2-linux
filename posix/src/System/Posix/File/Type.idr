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
fromMode m =
  case m .&. 61440 of
    32768 => Regular
    16384 => Directory
    8192 => CharDevice
    24576 => BlockDevice
    4096 => Pipe
    49152 => Socket
    40960 => Link
    _ => Other

public export
statvfs_size : Nat
statvfs_size = 112

public export
stat_size : Nat
stat_size = 144
