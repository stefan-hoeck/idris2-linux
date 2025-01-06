||| This provides a very basic implementation of interface `ErrIO` for `IO`.
|||
||| Note: This is useful for quick prototyping and when setting up resources
||| in a library but it sorely lacks versatility because there is no recovery
||| from error: The system just exits with an error message when an error is
||| encountered.
module System.Posix.Errno.IO

import Data.Linear.Token
import System.Posix.Errno
import System

%default total

fromEprim : EPrim a -> IO (Either Errno a)
fromEprim f =
  runIO $ \t => case f t of
    R v t => Right v # t
    E x t => Left x # t

export %inline
ErrIO IO where
  eprim act =
    fromEprim act >>= \case
      Left e  => die "\{errorText e} (\{errorName e})"
      Right v => pure v


