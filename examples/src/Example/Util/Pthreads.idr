module Example.Util.Pthreads

import public Example.Util.File
import public System.Posix.Pthreads

%default total

export %inline
Resource MutexT where
  cleanup = destroyMutex

export %inline
Resource CondT where
  cleanup = destroyCond
