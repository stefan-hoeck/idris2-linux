module System.Posix.Async

import public IO.Async

import Data.C.Ptr
import System.Posix.Dir
import System.Posix.File

%default total

--------------------------------------------------------------------------------
-- Implementations
--------------------------------------------------------------------------------

export %inline
Has Errno es => ErrIO (Async e es) where
  eprim act =
    sync $ fromPrim $ \w => case act w of
      R r w => MkIORes (Right r) w
      E x w => MkIORes (Left $ inject x) w

export %inline
Resource (CArrayIO n a) where
  cleanup = liftIO . free

export %inline
Struct a => Resource a where
  cleanup = freeStruct

export %inline
Resource Dir where
  cleanup d = dropErrs {es = [Errno]} (closedir d)

namespace Fd
  export %inline
  Cast a Fd => Resource a where
    cleanup fd = dropErrs {es = [Errno]} (close fd)
