#!/usr/bin/env bash

make -C codegen all
make -C support all

cat >src/System/Linux/Error/Type.idr <<EOT
-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Linux.Error.Type

import Derive.Finite
import Derive.Prelude

%default total
%language ElabReflection

EOT

codegen/error_gen >>src/System/Linux/Error/Type.idr

cat >src/System/Linux/File/Flags.idr <<EOT
-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Linux.File.Flags

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

codegen/flags_gen >>src/System/Linux/File/Flags.idr

cat >src/System/Linux/File/Whence.idr <<EOT
-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Linux.File.Whence

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

codegen/whence_gen >>src/System/Linux/File/Whence.idr

cat >src/System/Linux/Limits.idr <<EOT
-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Linux.Limits

import Data.C.Integer

%default total

export %foreign "C:sysconf, linux-idris"
sysconf : Bits32 -> Long

export %foreign "C:pathconf, linux-idris"
pathconf : String -> Bits32 -> Long

export %foreign "C:fpathconf, linux-idris"
fpathconf : Bits32 -> Bits32 -> Long
EOT

codegen/limits_gen >>src/System/Linux/Limits.idr

cat >src/System/Linux/File/Type.idr <<EOT
-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Linux.File.Type

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

codegen/filetype_gen >>src/System/Linux/File/Type.idr
