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


public export
mutexCode : MutexType -> Bits8
mutexCode MUTEX_NORMAL = 0
mutexCode MUTEX_RECURSIVE = 1
mutexCode MUTEX_ERRORCHECK = 2

public export
cancelType : CancelType -> Bits8
cancelType CANCEL_DEFERRED = 0
cancelType CANCEL_ASYNCHRONOUS = 1

public export
cancelState : CancelState -> Bits8
cancelState CANCEL_ENABLE = 0
cancelState CANCEL_DISABLE = 1

public export %inline
pthread_t_size : Bits32
pthread_t_size = 8

public export %inline
mutex_t_size : Bits32
mutex_t_size = 40

public export %inline
cond_t_size : Bits32
cond_t_size = 48
