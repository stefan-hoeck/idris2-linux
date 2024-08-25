#!/usr/bin/env bash

make -C codegen all

cat >src/System/Linux/Error.idr <<EOT
-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Linux.Error

import Data.SortedMap
import Derive.Finite
import Derive.Prelude

%default total
%language ElabReflection

EOT

codegen/error_gen >>src/System/Linux/Error.idr

cat >>src/System/Linux/Error.idr <<EOT

codeMap : SortedMap Bits32 Error
codeMap = SortedMap.fromList $ map (\x => (errorCode x, x)) values

export
fromCode : Bits32 -> Error
fromCode x = fromMaybe EOTHER (lookup x codeMap)
EOT
