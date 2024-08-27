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
whenceCode SEEK_SET = 0
whenceCode SEEK_CUR = 1
whenceCode SEEK_END = 2
