module System.Posix.File

import Data.Bits
import System.Posix.File.Prim as P

import public Data.Buffer
import public Data.Buffer.Core
import public Data.ByteString
import public Data.ByteVect

import public Data.C.Ptr

import public System.Posix.Errno
import public System.Posix.File.FileDesc
import public System.Posix.File.Flags
import public System.Posix.File.ReadRes
import public System.Posix.File.Whence

%default total

--------------------------------------------------------------------------------
-- File Operations
--------------------------------------------------------------------------------

||| Tries to open a file with the given flags and mode.
export %inline
openFile : Has Errno es => EIO1 f => String -> Flags -> Mode -> f es Fd
openFile p f m = elift1 (P.openFile p f m)

||| Convenience version of `close` that fails silently.
export %inline
close' : FileDesc a => HasIO io => (fd : a) -> io ()
close' fd = primIO (P.close' fd)

parameters {auto fid : FileDesc a}
           (fd       : a)
           {auto has : Has Errno es}
           {auto eoi : EIO1 f}

  ||| Closes a file descriptor.
  export %inline
  close : f es ()
  close = elift1 (P.close fd)

  ||| Reads at most `n` bytes from a file into a pre-allocated pointer.
  export %inline
  readPtr : (0 r : Type) -> FromPtr r => CPtr -> f es r
  readPtr r p = elift1 (P.readPtr fd r p)

  ||| Reads at most `n` bytes from a file into a pre-allocated pointer.
  export %inline
  readPtrRes : (0 r : Type) -> FromPtr r => CPtr -> f es (ReadRes r)
  readPtrRes r p = elift1 (P.readPtrRes fd r p)

  ||| Reads at most `n` bytes from a file into a bytestring.
  export %inline
  read : (0 r : Type) -> FromBuf r => (n : Bits32) -> f es r
  read r n = elift1 (P.read fd r n)

  ||| Reads at most `n` bytes from a file into a bytestring.
  |||
  ||| This is a more convenient version of `read` that gives detailed
  ||| information about why a read might fail. It is especially useful
  ||| when reading from - possibly non-blocking - pipes or sockets.
  export %inline
  readres : (0 r : Type) -> FromBuf r => (n : Bits32) -> f es (ReadRes r)
  readres r n = elift1 (P.readres fd r n)

  ||| Atomically reads up to `n` bytes from the given file at
  ||| the given file offset.
  |||
  ||| Notes: This will only work with seekable files but not with
  |||        arbitrary data streams such as pipes or sockets.
  |||        Also, it will not change the position of the open file description.
  export %inline
  pread : (0 r : Type) -> FromBuf r => (n : Bits32) -> OffT -> f es r
  pread r n o = elift1 (P.pread fd r n o)

  ||| Writes up to the number of bytes in the bytestring
  ||| to the given file.
  |||
  ||| Note: This is an atomic operation if `fd` is a regular file that
  |||       was opened in "append" mode (with the `O_APPEND` flag).
  export %inline
  write : ToBuf r => r -> f es Bits32
  write v = elift1 (P.write fd v)

  ||| Iteratively writes a value to a file descriptor making sure
  ||| that the whole value is written. Use this, if a single call to
  ||| `write` might not write the complete data (for instance, when
  ||| writing to a pipe or socket).
  export %inline
  fwrite : ToBuf r => r -> f es ()
  fwrite v = elift1 (P.fwrite fd v)

  ||| Atomically writes up to the number of bytes in the bytestring
  ||| to the given file at the given file offset.
  |||
  ||| Notes: This will only work with seekable files but not with
  |||        arbitrary data streams such as pipes or sockets.
  |||        Also, it will not change the position of the open file description.
  export
  pwrite : ToBuf r => r -> OffT -> f es Bits32
  pwrite bs o = elift1 (P.pwrite fd bs o)


--------------------------------------------------------------------------------
-- File seeking
--------------------------------------------------------------------------------

||| Moves the file pointer to the given offset relative to the
||| `Whence` value.
export %inline
lseek : FileDesc a => HasIO io => (fd : a) -> OffT -> Whence -> io OffT
lseek fd offset whence = primIO (P.lseek fd offset whence)

--------------------------------------------------------------------------------
-- Duplicating file descriptors
--------------------------------------------------------------------------------

parameters {auto fid : FileDesc a}
           (fd       : a)
           {auto has : Has Errno es}
           {auto eoi : EIO1 f}

  ||| Duplicates the given open file descriptor.
  |||
  ||| The duplicate is guaranteed to be given the smallest available
  ||| file descriptor.
  export %inline
  dup : f es Fd
  dup = elift1 (P.dup fd)

  ||| Duplicates the given open file descriptor.
  |||
  ||| The new file descriptor vill have the integer value of `fd2`.
  ||| This is an atomic operation that will close `fd2` if it is still open.
  export %inline
  dup2 : FileDesc b => (fd2 : b) -> f es Fd
  dup2 fd2 = elift1 (P.dup2 fd fd2)

  ||| Duplicates the given open file descriptor.
  |||
  ||| The new file descriptor vill have the integer value of `fd2`.
  ||| This is an atomic operation that will close `fd2` if it is still open.
  export %inline
  dupfd : (start : Bits32) -> f es Fd
  dupfd start = elift1 (P.dupfd fd start)

--------------------------------------------------------------------------------
-- Setting and getting file flags
--------------------------------------------------------------------------------

  ||| Gets the flags set at an open file descriptor.
  export
  getFlags : f es Flags
  getFlags = elift1 (P.getFlags fd)

  ||| Sets the flags of an open file descriptor.
  |||
  ||| Note: This replaces the currently set flags. See also `addFlags`.
  export %inline
  setFlags : Flags -> f es ()
  setFlags fs = elift1 (P.setFlags fd fs)

  ||| Adds the given flags to the flags set for an open
  ||| file descriptor by ORing them with the currently set flags.
  export
  addFlags : Flags -> f es ()
  addFlags fs = elift1 (P.addFlags fd fs)

  ||| Truncates a file to the given length.
  export %inline
  ftruncate : OffT -> f es ()
  ftruncate o = elift1 (P.ftruncate fd o)

||| Truncates a file to the given length.
export %inline
truncate : Has Errno es => EIO1 f => String -> OffT -> f es ()
truncate s o = elift1 (P.truncate s o)

||| Atomically creates and opens a temporary, unique file.
export
mkstemp : Has Errno es => EIO1 f => String -> f es (Fd, String)
mkstemp s = elift1 (P.mkstemp s)

--------------------------------------------------------------------------------
-- Links
--------------------------------------------------------------------------------

||| Creates a (hard) link to a file.
export %inline
link : Has Errno es => EIO1 f => (file, link : String) -> f es ()
link f l = elift1 (P.link f l)

||| Creates a (hard) link to a file.
export %inline
symlink : Has Errno es => EIO1 f => (file, link : String) -> f es ()
symlink f l = elift1 (P.symlink f l)

||| Deletes a (hard) link to a file.
|||
||| If this is the last link to the file, the file is removed.
|||
||| Note: Files with open file descriptors will only be deleted after the last
|||       open file descriptor is closed, but the file name will already
|||       disapper from the file system before that.
export %inline
unlink : Has Errno es => EIO1 f => (file : String) -> f es ()
unlink file = elift1 (P.unlink file)

||| Removes a file or (empty) directory calling `unlink` or `rmdir`
||| internally.
export %inline
remove : Has Errno es => EIO1 f => (file : String) -> f es ()
remove file = elift1 (P.remove file)

||| Renames a file within a file system.
|||
||| Note: This will fail if the two paths point to different file systems.
|||       In that case, the file needs to be copied from one FS to the other.
export %inline
rename : Has Errno es => EIO1 f => (file, link : String) -> f es ()
rename f l = elift1 (P.rename f l)

||| Returns the path of a file a symbolic link points to
|||
||| This allocates a buffer of 4096 bytes for the byte array holding
||| the result.
export %inline
readlink : Has Errno es => EIO1 f => (file : String) -> f es ByteString
readlink file = elift1 (P.readlink file)

--------------------------------------------------------------------------------
-- Standard input and output
--------------------------------------------------------------------------------

parameters {auto hio : HasIO io}

  export %inline
  stdout : String -> io ()
  stdout = primIO . P.stdout

  export %inline
  stdoutLn : String -> io ()
  stdoutLn = primIO . P.stdoutLn

  export %inline
  prnt : Show a => a -> io ()
  prnt = primIO . P.prnt

  export %inline
  prntLn : Show a => a -> io ()
  prntLn = primIO . P.prntLn

  export %inline
  stderr : String -> io ()
  stderr = primIO . P.stderr

  export %inline
  stderrLn : String -> io ()
  stderrLn = primIO . P.stderrLn
