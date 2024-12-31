module System.Posix.File.Prim

import Data.Bits

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
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_open, posix-idris"
prim__open : String -> Bits32 -> ModeT -> PrimIO CInt

%foreign "C:li_close, posix-idris"
prim__close : Bits32 -> PrimIO CInt

%foreign "C__collect_safe:li_read, posix-idris"
prim__readptr : (file : Bits32) -> AnyPtr -> (max : Bits32) -> PrimIO SsizeT

%foreign "C:li_read, posix-idris"
prim__read : (file : Bits32) -> Buffer -> (max : Bits32) -> PrimIO SsizeT

%foreign "C:li_pread, posix-idris"
prim__pread : (file : Bits32) -> Buffer -> (max : Bits32) -> OffT -> PrimIO SsizeT

%foreign "C:li_write, posix-idris"
prim__write : (file : Bits32) -> Buffer -> (off,max : Bits32) -> PrimIO SsizeT

%foreign "C__collect_safe:li_write, posix-idris"
prim__writeptr : (file : Bits32) -> AnyPtr -> (off,max : Bits32) -> PrimIO SsizeT

%foreign "C:li_pwrite, posix-idris"
prim__pwrite : (file : Bits32) -> Buffer -> (off,max : Bits32) -> OffT -> PrimIO SsizeT

%foreign "C:lseek, posix-idris"
prim__lseek : (file : Bits32) -> (off : OffT) -> (whence : CInt) -> PrimIO OffT

%foreign "C:li_set_flags, posix-idris"
prim__setFlags : (file : Bits32) -> (flags : Bits32) -> PrimIO CInt

%foreign "C:li_get_flags, posix-idris"
prim__getFlags : (file : Bits32) -> PrimIO CInt

%foreign "C:li_dup, posix-idris"
prim__dup : (file : Bits32) -> PrimIO CInt

%foreign "C:li_dup2, posix-idris"
prim__dup2 : (file, dst : Bits32) -> PrimIO CInt

%foreign "C:li_dupfd, posix-idris"
prim__dupfd : (file, startfd : Bits32) -> PrimIO CInt

%foreign "C:li_ftruncate, posix-idris"
prim__ftruncate : (file : Bits32) -> (len : OffT) -> PrimIO CInt

%foreign "C:li_truncate, posix-idris"
prim__truncate : (file : String) -> (len : OffT) -> PrimIO CInt

%foreign "C:li_mkstemp, posix-idris"
prim__mkstemp : Buffer -> PrimIO CInt

%foreign "C:li_link, posix-idris"
prim__link : String -> String -> PrimIO CInt

%foreign "C:li_symlink, posix-idris"
prim__symlink : String -> String -> PrimIO CInt

%foreign "C:li_rename, posix-idris"
prim__rename : String -> String -> PrimIO CInt

%foreign "C:li_unlink, posix-idris"
prim__unlink : String -> PrimIO CInt

%foreign "C:li_remove, posix-idris"
prim__remove : String -> PrimIO CInt

%foreign "C:li_readlink, posix-idris"
prim__readlink : (file : String) -> Buffer -> (max : Bits32) -> PrimIO SsizeT

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

||| Converts a number of bytes read into a buffer to a `ByteString`
export %inline
toBytes : Bits32 -> (Buffer -> Bits32 -> PrimIO SsizeT) -> EPrim ByteString
toBytes n act w =
  let MkIORes buf w := prim__newBuf n w
      MkIORes rd  w := act buf n w
   in if rd < 0
         then E (fromNeg rd) w
         else R (unsafeByteString (cast rd) buf) w

export %inline
toFD : PrimIO CInt -> EPrim Fd
toFD = toVal (MkFd . cast)

--------------------------------------------------------------------------------
-- File Operations
--------------------------------------------------------------------------------

||| Tries to open a file with the given flags and mode.
export %inline
openFile : String -> Flags -> Mode -> EPrim Fd
openFile p (F f) (M m) = toFD (prim__open p f m)

parameters {auto fid : FileDesc a}
           (fd       : a)

  ||| Closes a file descriptor.
  export %inline
  close : EPrim ()
  close = toUnit (prim__close $ fileDesc fd)

  ||| Convenience version of `close` that fails silently.
  export %inline
  close' : PrimIO ()
  close' w =
    let MkIORes _ w := prim__close (fileDesc fd) w
     in MkIORes () w

  ||| Reads at most `n` bytes from a file into an allocated pointer.
  export %inline
  readPtr : AnyPtr -> (n : Bits32) -> EPrim Bits32
  readPtr ptr n = toSize $ prim__readptr (fileDesc fd) ptr n

  ||| Reads at most `n * sizeof a` bytes into a preallocated array.
  export
  readArr : {n : _} -> SizeOf b => CArrayIO n b -> EPrim (k ** CArrayIO k b)
  readArr p w =
    let ptr    := unsafeUnwrap p
        sz     := sizeof b
        R bs w := readPtr ptr (cast n * sz) w | E x w => E x w
        k      := cast (bs `div` sz)
     in R (k ** unsafeWrap ptr) w

  ||| Reads at most `n * sizeof a` bytes into a preallocated array and
  ||| converts it to a list of values.
  export
  readVals :
       {n : _}
    -> {auto sof : SizeOf b}
    -> {auto der : Deref b}
    -> CArrayIO n b
    -> (b -> PrimIO c)
    -> EPrim (List c)
  readVals p f w =
    let R (k ** arr) w := readArr p w | E x w => E x w
        MkIORes vs   w := values [] arr f k w
     in R vs w

  ||| Reads at most `n` bytes from a file into a buffer.
  export %inline
  readRaw : Buffer -> (n : Bits32) -> EPrim (k ** IOBuffer k)
  readRaw buf n w =
    let R sz w := toSize (prim__read (fileDesc fd) buf n) w | E x w => E x w
     in R (cast sz ** unsafeMBuffer buf) w

  ||| Reads at most `n` bytes from a file into a bytestring.
  export
  read : (n : Bits32) -> EPrim ByteString
  read n = toBytes n $  prim__read (fileDesc fd)

  ||| Atomically reads up to `n` bytes from the given file at
  ||| the given file offset.
  |||
  ||| Notes: This will only work with seekable files but not with
  |||        arbitrary data streams such as pipes or sockets.
  |||        Also, it will not change the position of the open file description.
  export
  pread : (n : Bits32) -> OffT -> EPrim ByteString
  pread n off = toBytes n $ \b,x => prim__pread (fileDesc fd) b x off

  ||| Writes up to the number of bytes in the bytestring
  ||| to the given file.
  |||
  ||| Note: This is an atomic operation if `fd` is a regular file that
  |||       was opened in "append" mode (with the `O_APPEND` flag).
  export
  writeBytes : ByteString -> EPrim Bits32
  writeBytes (BS n $ BV b o _) =
    toSize $ prim__write (fileDesc fd) (unsafeGetBuffer b) (cast o) (cast n)

  ||| Writes up to the given number of bytes from the given buffer starting
  ||| at the given offset.
  |||
  ||| Note: This is an atomic operation if `fd` is a regular file that
  |||       was opened in "append" mode (with the `O_APPEND` flag).
  export %inline
  writeRaw : Buffer -> (offset,n : Bits32) -> EPrim Bits32
  writeRaw buf o n = toSize $ prim__write (fileDesc fd) buf o n

  ||| Writes up to the number of bytes from the given C ptr.
  |||
  ||| Note: This is an atomic operation if `fd` is a regular file that
  |||       was opened in "append" mode (with the `O_APPEND` flag).
  export %inline
  writePtr : AnyPtr -> (n : Bits32) -> EPrim Bits32
  writePtr buf n = toSize $ prim__writeptr (fileDesc fd) buf 0 n

  ||| Writes the content of the given array.
  |||
  ||| Note: This is an atomic operation if `fd` is a regular file that
  |||       was opened in "append" mode (with the `O_APPEND` flag).
  export %inline
  writeArr : {n : _} -> SizeOf b => CArrayIO n b -> EPrim Bits32
  writeArr p = writePtr (unsafeUnwrap p) (cast n * sizeof b)


  ||| Atomically writes up to the number of bytes in the bytestring
  ||| to the given file at the given file offset.
  |||
  ||| Notes: This will only work with seekable files but not with
  |||        arbitrary data streams such as pipes or sockets.
  |||        Also, it will not change the position of the open file description.
  export
  pwriteBytes : ByteString -> OffT -> EPrim Bits32
  pwriteBytes (BS n $ BV b o _) off =
    toSize $ prim__pwrite (fileDesc fd) (unsafeGetBuffer b) (cast o) (cast n) off

  export %inline
  write : {n : _} -> IBuffer n -> EPrim Bits32
  write ibuf = writeRaw (unsafeGetBuffer ibuf) 0 (cast n)

  export %inline
  writeIO : {n : _} -> IOBuffer n -> EPrim Bits32
  writeIO mbuf = writeRaw (unsafeFromMBuffer mbuf) 0 (cast n)

  export %inline
  writeStr : String -> EPrim Bits32
  writeStr = writeBytes . fromString

  export %inline
  writeStrLn : String -> EPrim Bits32
  writeStrLn = writeStr . (++ "\n")

--------------------------------------------------------------------------------
-- File seeking
--------------------------------------------------------------------------------

  ||| Moves the file pointer to the given offset relative to the
  ||| `Whence` value.
  export %inline
  lseek : OffT -> Whence -> PrimIO OffT
  lseek offset whence =
    prim__lseek (fileDesc fd) offset (cast $ whenceCode whence)

--------------------------------------------------------------------------------
-- Duplicating file descriptors
--------------------------------------------------------------------------------

  ||| Duplicates the given open file descriptor.
  |||
  ||| The duplicate is guaranteed to be given the smallest available
  ||| file descriptor.
  export %inline
  dup : EPrim Fd
  dup = toFD $ prim__dup (fileDesc fd)

  ||| Duplicates the given open file descriptor.
  |||
  ||| The new file descriptor vill have the integer value of `fd2`.
  ||| This is an atomic operation that will close `fd2` if it is still open.
  export %inline
  dup2 : FileDesc b => (fd2 : b) -> EPrim Fd
  dup2 fd2 = toFD $ prim__dup2 (fileDesc fd) (fileDesc fd2)

  ||| Duplicates the given open file descriptor.
  |||
  ||| The new file descriptor vill have the integer value of `fd2`.
  ||| This is an atomic operation that will close `fd2` if it is still open.
  export %inline
  dupfd : (start : Bits32) -> EPrim Fd
  dupfd fd2 = toFD $ prim__dupfd (fileDesc fd) fd2

--------------------------------------------------------------------------------
-- Setting and getting file flags
--------------------------------------------------------------------------------

  ||| Gets the flags set at an open file descriptor.
  export
  getFlags : EPrim Flags
  getFlags w =
   let MkIORes r w := prim__getFlags (fileDesc fd) w
    in if r < 0 then E (fromNeg r) w else R (F $ cast r) w

  ||| Sets the flags of an open file descriptor.
  |||
  ||| Note: This replaces the currently set flags. See also `addFlags`.
  export %inline
  setFlags : Flags -> EPrim ()
  setFlags (F fs) = toUnit $ prim__setFlags (fileDesc fd) fs

  ||| Adds the given flags to the flags set for an open
  ||| file descriptor by ORing them with the currently set flags.
  export
  addFlags : Flags -> EPrim ()
  addFlags fs w =
    let R x w := getFlags w | E x w => E x w
     in setFlags (x <+> fs) w

  ||| Truncates a file to the given length.
  export %inline
  ftruncate : OffT -> EPrim ()
  ftruncate len = toUnit $ prim__ftruncate (fileDesc fd) len

||| Truncates a file to the given length.
export %inline
truncate : String -> OffT -> EPrim ()
truncate f len = toUnit $ prim__truncate f len

||| Atomically creates and opens a temporary, unique file.
export
mkstemp : String -> EPrim (Fd, String)
mkstemp f w =
  let pat := "\{f}XXXXXX"
      len := stringByteLength pat
      MkIORes buf w := prim__newBuf (cast len) w
      MkIORes _ w   := toPrim (setString buf 0 pat) w
      R fd w := toFD (prim__mkstemp buf) w | E x w => E x w
      MkIORes str w :=  toPrim (getString buf 0 len) w
   in R (fd, str) w

--------------------------------------------------------------------------------
-- Links
--------------------------------------------------------------------------------

||| Creates a (hard) link to a file.
export %inline
link : (file, link : String) -> EPrim ()
link f l = toUnit $ prim__link f l

||| Creates a (hard) link to a file.
export %inline
symlink : (file, link : String) -> EPrim ()
symlink f l = toUnit $ prim__symlink f l

||| Deletes a (hard) link to a file.
|||
||| If this is the last link to the file, the file is removed.
|||
||| Note: Files with open file descriptors will only be deleted after the last
|||       open file descriptor is closed, but the file name will already
|||       disapper from the file system before that.
export %inline
unlink : (file : String) -> EPrim ()
unlink f = toUnit $ prim__unlink f

||| Removes a file or (empty) directory calling `unlink` or `rmdir`
||| internally.
export %inline
remove : (file : String) -> EPrim ()
remove f = toUnit $ prim__remove f

||| Renames a file within a file system.
|||
||| Note: This will fail if the two paths point to different file systems.
|||       In that case, the file needs to be copied from one FS to the other.
export %inline
rename : (file, link : String) -> EPrim ()
rename f l = toUnit $ prim__rename f l

||| Returns the path of a file a symbolic link points to
|||
||| This allocates a buffer of 4096 bytes for the byte array holding
||| the result.
export %inline
readlink : (file : String) -> EPrim ByteString
readlink f = toBytes 4096 $ prim__readlink f

--------------------------------------------------------------------------------
-- Standard input and output
--------------------------------------------------------------------------------

export %inline
stdout : String -> PrimIO ()
stdout s = ignore $ writeStr Stdout s

export %inline
stdoutLn : String -> PrimIO ()
stdoutLn s = ignore $ writeStrLn Stdout s

export %inline
prnt : Show a => a -> PrimIO ()
prnt = stdout . show

export %inline
prntLn : Show a => a -> PrimIO ()
prntLn = stdoutLn . show

export %inline
stderr : String -> PrimIO ()
stderr s = ignore $ writeStr Stderr s

export %inline
stderrLn : String -> PrimIO ()
stderrLn s = ignore $ writeStrLn Stderr s
