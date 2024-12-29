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
import public System.Posix.File.Whence

%default total

--------------------------------------------------------------------------------
-- File Operations
--------------------------------------------------------------------------------

||| Tries to open a file with the given flags and mode.
export %inline
openFile : ErrIO io => String -> Flags -> Mode -> io Fd
openFile p f = eprim . P.openFile p f

||| Convenience version of `close` that fails silently.
export %inline
close' : FileDesc a => HasIO io => (fd : a) -> io ()
close' fd = primIO (P.close' fd)

parameters {auto fid : FileDesc a}
           (fd       : a)
           {auto eoi : ErrIO io}

  ||| Closes a file descriptor.
  export %inline
  close : io ()
  close = eprim (P.close fd)

  ||| Reads at most `n` bytes from a file into an allocated pointer.
  export %inline
  readPtr : AnyPtr -> (n : Bits32) -> io Bits32
  readPtr ptr = eprim . P.readPtr fd ptr

  ||| Reads at most `n * sizeof a` bytes into a preallocated array.
  export %inline
  readArr : {n : _} -> SizeOf b => CArrayIO n b -> io (k ** CArrayIO k b)
  readArr = eprim . P.readArr fd

  ||| Reads at most `n * sizeof a` bytes into a preallocated array and
  ||| converts it to a list of values.
  export %inline
  readVals :
       {n : _}
    -> {auto sof : SizeOf b}
    -> {auto der : Deref b}
    -> CArrayIO n b
    -> (b -> PrimIO c)
    -> io (List c)
  readVals p = eprim . P.readVals fd p

  ||| Reads at most `n` bytes from a file into a buffer.
  export %inline
  readRaw : Buffer -> (n : Bits32) -> io (k ** IOBuffer k)
  readRaw buf = eprim . P.readRaw fd buf

  ||| Reads at most `n` bytes from a file into a bytestring.
  export %inline
  read : (n : Bits32) -> io ByteString
  read = eprim . P.read fd

  ||| Atomically reads up to `n` bytes from the given file at
  ||| the given file offset.
  |||
  ||| Notes: This will only work with seekable files but not with
  |||        arbitrary data streams such as pipes or sockets.
  |||        Also, it will not change the position of the open file description.
  export %inline
  pread : (n : Bits32) -> OffT -> io ByteString
  pread n = eprim . P.pread fd n

  ||| Writes up to the number of bytes in the bytestring
  ||| to the given file.
  |||
  ||| Note: This is an atomic operation if `fd` is a regular file that
  |||       was opened in "append" mode (with the `O_APPEND` flag).
  export %inline
  writeBytes : ByteString -> io Bits32
  writeBytes = eprim . P.writeBytes fd

  ||| Writes up to the given number of bytes from the given buffer starting
  ||| at the given offset.
  |||
  ||| Note: This is an atomic operation if `fd` is a regular file that
  |||       was opened in "append" mode (with the `O_APPEND` flag).
  export %inline
  writeRaw : Buffer -> (offset,n : Bits32) -> io Bits32
  writeRaw buf o = eprim . P.writeRaw fd buf o

  ||| Writes up to the number of bytes from the given C ptr.
  |||
  ||| Note: This is an atomic operation if `fd` is a regular file that
  |||       was opened in "append" mode (with the `O_APPEND` flag).
  export %inline
  writePtr : AnyPtr -> (n : Bits32) -> io Bits32
  writePtr buf = eprim . P.writePtr fd buf

  ||| Writes the content of the given array.
  |||
  ||| Note: This is an atomic operation if `fd` is a regular file that
  |||       was opened in "append" mode (with the `O_APPEND` flag).
  export %inline
  writeArr : {n : _} -> SizeOf b => CArrayIO n b -> io Bits32
  writeArr p = eprim (P.writeArr fd p)


  ||| Atomically writes up to the number of bytes in the bytestring
  ||| to the given file at the given file offset.
  |||
  ||| Notes: This will only work with seekable files but not with
  |||        arbitrary data streams such as pipes or sockets.
  |||        Also, it will not change the position of the open file description.
  export
  pwriteBytes : ByteString -> OffT -> io Bits32
  pwriteBytes bs = eprim . P.pwriteBytes fd bs

  export %inline
  write : {n : _} -> IBuffer n -> io Bits32
  write = eprim . P.write fd

  export %inline
  writeStr : String -> io Bits32
  writeStr = eprim . P.writeStr fd

  export %inline
  writeStrLn : String -> io Bits32
  writeStrLn = eprim . P.writeStrLn fd

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
           {auto eoi : ErrIO io}

  ||| Duplicates the given open file descriptor.
  |||
  ||| The duplicate is guaranteed to be given the smallest available
  ||| file descriptor.
  export %inline
  dup : io Fd
  dup = eprim (P.dup fd)

  ||| Duplicates the given open file descriptor.
  |||
  ||| The new file descriptor vill have the integer value of `fd2`.
  ||| This is an atomic operation that will close `fd2` if it is still open.
  export %inline
  dup2 : FileDesc b => (fd2 : b) -> io Fd
  dup2 = eprim . P.dup2 fd

  ||| Duplicates the given open file descriptor.
  |||
  ||| The new file descriptor vill have the integer value of `fd2`.
  ||| This is an atomic operation that will close `fd2` if it is still open.
  export %inline
  dupfd : (start : Bits32) -> io Fd
  dupfd = eprim . P.dupfd fd

--------------------------------------------------------------------------------
-- Setting and getting file flags
--------------------------------------------------------------------------------

  ||| Gets the flags set at an open file descriptor.
  export
  getFlags : io Flags
  getFlags = eprim (P.getFlags fd)

  ||| Sets the flags of an open file descriptor.
  |||
  ||| Note: This replaces the currently set flags. See also `addFlags`.
  export %inline
  setFlags : Flags -> io ()
  setFlags = eprim . P.setFlags fd

  ||| Adds the given flags to the flags set for an open
  ||| file descriptor by ORing them with the currently set flags.
  export
  addFlags : Flags -> io ()
  addFlags = eprim . P.addFlags fd

  ||| Truncates a file to the given length.
  export %inline
  ftruncate : OffT -> io ()
  ftruncate = eprim . P.ftruncate fd

||| Truncates a file to the given length.
export %inline
truncate : ErrIO io => String -> OffT -> io ()
truncate s = eprim . P.truncate s

||| Atomically creates and opens a temporary, unique file.
export
mkstemp : ErrIO io => String -> io (Fd, String)
mkstemp = eprim . P.mkstemp

--------------------------------------------------------------------------------
-- Links
--------------------------------------------------------------------------------

||| Creates a (hard) link to a file.
export %inline
link : ErrIO io => (file, link : String) -> io ()
link f = eprim . P.link f

||| Creates a (hard) link to a file.
export %inline
symlink : ErrIO io => (file, link : String) -> io ()
symlink f = eprim . P.symlink f

||| Deletes a (hard) link to a file.
|||
||| If this is the last link to the file, the file is removed.
|||
||| Note: Files with open file descriptors will only be deleted after the last
|||       open file descriptor is closed, but the file name will already
|||       disapper from the file system before that.
export %inline
unlink : ErrIO io => (file : String) -> io ()
unlink = eprim . P.unlink

||| Removes a file or (empty) directory calling `unlink` or `rmdir`
||| internally.
export %inline
remove : ErrIO io => (file : String) -> io ()
remove = eprim . P.remove

||| Renames a file within a file system.
|||
||| Note: This will fail if the two paths point to different file systems.
|||       In that case, the file needs to be copied from one FS to the other.
export %inline
rename : ErrIO io => (file, link : String) -> io ()
rename f = eprim . P.rename f

||| Returns the path of a file a symbolic link points to
|||
||| This allocates a buffer of 4096 bytes for the byte array holding
||| the result.
export %inline
readlink : ErrIO io => (file : String) -> io ByteString
readlink = eprim . P.readlink

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
