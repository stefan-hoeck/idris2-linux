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

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Creates a new directory.
|||
||| This fails if the directory exists already. It also fails, if the
||| parent directory does not exist.
export %inline
mkdir : ErrIO io => (pth : String) -> Mode -> io ()
mkdir pth = eprim . P.mkdir pth

||| Opens a directory.
export
opendir : ErrIO io => String -> io Dir
opendir = eprim . P.opendir

||| Opens a directory from a file descriptor.
export
fdopendir : FileDesc a => ErrIO io => a -> io Dir
fdopendir = eprim . P.fdopendir

||| Closes a directory.
export
rewinddir : HasIO io => Dir -> io ()
rewinddir = primIO . P.rewinddir

||| Closes a directory.
export
closedir : ErrIO io => Dir -> io ()
closedir = eprim . P.closedir

||| Reads the next entry from a directory.
export
readdir : (0 r : Type) -> FromBuf r => ErrIO io => Dir -> io (ReadRes r)
readdir r = eprim . P.readdir r

||| Returns the current working directory.
export %inline
getcwd : (0 r : Type) -> FromBuf r => ErrIO io => io r
getcwd r = eprim $ P.getcwd r

||| Changes the current working directory
export
chdir : ErrIO io => String -> io ()
chdir = eprim . P.chdir

||| Changes the current working directory
export
chroot : ErrIO io => String -> io ()
chroot = eprim . P.chroot
