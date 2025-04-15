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


public export %inline
timespec_size : Bits32
timespec_size = 16

public export %inline
tm_size : Bits32
tm_size = 56
