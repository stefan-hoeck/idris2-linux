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
mutexCode : MutexType -> Bits8
mutexCode MUTEX_NORMAL = 0
mutexCode MUTEX_RECURSIVE = 1
mutexCode MUTEX_ERRORCHECK = 2

public export %inline
pthread_t_size : Nat
pthread_t_size = 8

public export %inline
mutex_t_size : Nat
mutex_t_size = 40

public export %inline
cond_t_size : Nat
cond_t_size = 48
