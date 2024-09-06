module Example.Util.Timer

import Derive.Finite
import Derive.Prelude
import public Example.Util.File
import public System.Posix.Timer

%default total
%language ElabReflection

export %inline
Resource Timeval where cleanup = freeTimeval

export %inline
Resource Itimerval where cleanup = freeItimerval
