module System.Posix.Dir

import Data.Buffer
import System.Posix.Dir.Prim as P

import public Data.Buffer.Core
import public Data.ByteString
import public Data.C.Integer
import public System.Posix.Dir.Dir
import public System.Posix.Errno
import public System.Posix.File

%default total

export %inline
ELift1 World f => Resource f Dir where
  cleanup d = lift1 $ closedir' d

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Creates a new directory.
|||
||| This fails if the directory exists already. It also fails, if the
||| parent directory does not exist.
export %inline
mkdir : Has Errno es => EIO1 f => (pth : String) -> Mode -> f es ()
mkdir pth m = elift1 (P.mkdir pth m)

||| Opens a directory.
export
opendir : Has Errno es => EIO1 f => String -> f es Dir
opendir s = elift1 (P.opendir s)

||| Opens a directory from a file descriptor.
export
fdopendir : FileDesc a => Has Errno es => EIO1 f => a -> f es Dir
fdopendir v = elift1 (P.fdopendir v)

||| Closes a directory.
export
rewinddir : HasIO io => Dir -> io ()
rewinddir = primIO . P.rewinddir

||| Closes a directory.
export
closedir : Has Errno es => EIO1 f => Dir -> f es ()
closedir d = elift1 (P.closedir d)

||| Reads the next entry from a directory.
export
readdir : (0 r : Type) -> FromBuf r => Has Errno es => EIO1 f => Dir -> f es (ReadRes r)
readdir r d = elift1 (P.readdir r d)

||| Returns the current working directory.
export %inline
getcwd : (0 r : Type) -> FromBuf r => Has Errno es => EIO1 f => f es r
getcwd r = elift1 (P.getcwd r)

||| Changes the current working directory
export
chdir : Has Errno es => EIO1 f => String -> f es ()
chdir s = elift1 (P.chdir s)

||| Changes the current working directory
export
chroot : Has Errno es => EIO1 f => String -> f es ()
chroot s = elift1 (P.chroot s)
