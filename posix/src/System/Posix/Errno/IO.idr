||| This provides a very basic implementation of interface `ErrIO` for `IO`.
|||
||| Note: This is useful for quick prototyping and when setting up resources
||| in a library but it sorely lacks versatility because there is no recovery
||| from error: The system just exits with an error message when an error is
||| encountered.
module System.Posix.Errno.IO

import System.Posix.Errno
import System

%default total

export %inline
ErrIO IO where
  error e = die "\{errorText e} (\{errorName e})"


