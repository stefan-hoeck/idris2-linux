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
import public System.Posix.File.ReadRes
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

%foreign "C__collect_safe:li_pwrite, posix-idris"
prim__pwriteptr : (file : Bits32) -> AnyPtr -> (off,max : Bits32) -> OffT -> PrimIO SsizeT

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

||| Converts a number of bytes read into a buffer to a suitable result.
export %inline
allocRead : FromBuf a => Bits32 -> (Buffer -> Bits32 -> PrimIO SsizeT) -> EPrim a
allocRead n act t =
  let buf # t := toF1 (prim__newBuf n) t
      rd  # t := toF1 (act buf n) t
   in if rd < 0
         then E (inject $ fromNeg rd) t
         else let r # t := fromBuf (B (cast rd) buf) t in R r t

||| Like `allocRead` but treats certain errors as valid results.
export %inline
toRes :
     {auto fb : FromBuf a}
  -> Bits32
  -> (Buffer -> Bits32 -> PrimIO SsizeT)
  -> EPrim (ReadRes a)
toRes n act t =
  let buf # t := toF1 (prim__newBuf n) t
      rd  # t := toF1 (act buf n) t
   in if      rd < 0  then fromErr (fromNeg rd) t
      else if rd == 0 then R EOI t
      else let r # t := fromBuf (B (cast rd) buf) t in R (Res r) t


||| Converts a number of bytes read into a C-ptr to a suitable result.
export %inline
ptrRead : FromPtr a => AnyPtr -> PrimIO SsizeT -> EPrim a
ptrRead ptr act t =
  let rd  # t := toF1 act t
   in if rd < 0
         then E (inject $ fromNeg rd) t
         else let res # t := fromPtr (CP (cast rd) ptr) t in R res t

||| Like `ptrRead` but treats certain errors as valid results.
export %inline
ptrToRes : FromPtr a => AnyPtr -> PrimIO SsizeT -> EPrim (ReadRes a)
ptrToRes ptr act t =
  let rd  # t := toF1 act t
   in if      rd < 0  then fromErr (fromNeg rd) t
      else if rd == 0 then R EOI t
      else let res # t := fromPtr (CP (cast rd) ptr) t  in R (Res res) t

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

  ||| Reads at most `n` bytes from a file into a pre-allocated pointer.
  export %inline
  readPtr : (0 r : Type) -> FromPtr r => CPtr -> EPrim r
  readPtr r (CP sz p) = ptrRead p $ prim__readptr (fileDesc fd) p sz

  ||| Reads at most `n` bytes from a file into a pre-allocated pointer.
  |||
  ||| This is similar to `readres`, but it allows us to efficiently stream
  ||| data into a large pointer, even in case the chunks of data are much smaller.
  export %inline
  readPtrRes : (0 r : Type) -> FromPtr r => CPtr -> EPrim (ReadRes r)
  readPtrRes r (CP sz p) = ptrToRes p $ prim__readptr (fileDesc fd) p sz

  ||| Reads at most `n` bytes from a file into a suitable result type.
  export
  read : (0 r : Type) -> FromBuf r => (n : Bits32) -> EPrim r
  read r n = allocRead n $  prim__read (fileDesc fd)

  ||| Reads at most `n` bytes from a file into a suitable result type.
  |||
  ||| This is a more convenient version of `read` that gives detailed
  ||| information about why a read might fail. It is especially useful
  ||| when reading from - possibly non-blocking - pipes or sockets.
  export
  readres : (0 r : Type) -> FromBuf r => (n : Bits32) -> EPrim (ReadRes r)
  readres r n = toRes n $  prim__read (fileDesc fd)

  ||| Atomically reads up to `n` bytes from the given file at
  ||| the given file offset.
  |||
  ||| Notes: This will only work with seekable files but not with
  |||        arbitrary data streams such as pipes or sockets.
  |||        Also, it will not change the position of the open file description.
  export
  pread : (0 r : Type) -> FromBuf r => (n : Bits32) -> OffT -> EPrim r
  pread r n off = allocRead n $ \b,x => prim__pread (fileDesc fd) b x off

  ||| Writes up to the number of bytes in the bytestring
  ||| to the given file.
  |||
  ||| Note: This is an atomic operation if `fd` is a regular file that
  |||       was opened in "append" mode (with the `O_APPEND` flag).
  export
  write : ToBuf r => r -> EPrim Bits32
  write v =
    case unsafeToBuf v of
      Left (CP sz ptr)        =>
        toSize $ prim__writeptr (fileDesc fd) ptr 0 sz
      Right (BS n $ BV b o _) =>
        toSize $ prim__write (fileDesc fd) (unsafeGetBuffer b) (cast o) (cast n)

  ||| Iteratively writes a value to a file descriptor making sure
  ||| that the whole value is written. Use this, if a single call to
  ||| `write` might not write the complete data (for instance, when
  ||| writing to a pipe or socket).
  export
  fwrite : ToBuf r => r -> EPrim ()
  fwrite v =
    case (unsafeToBuf v) of
      Left  (CP sz p) => goPtr p sz
      Right bs        => go bs

    where
      goPtr : AnyPtr -> Bits32 -> EPrim ()
      goPtr p 0  t = R () t
      goPtr p sz t =
        let R m t := write (CP sz p) t | E x t => E x t
         in goPtr (prim__inc_ptr p m 1) (assert_smaller sz $ sz - m) t

      go : ByteString -> EPrim ()
      go (BS 0 _) t = R () t
      go bs       t =
        let R m t := write bs t | E x t => E x t
         in go (assert_smaller bs $ drop (cast m) bs) t

  ||| Atomically writes up to the number of bytes in the bytestring
  ||| to the given file at the given file offset.
  |||
  ||| Notes: This will only work with seekable files but not with
  |||        arbitrary data streams such as pipes or sockets.
  |||        Also, it will not change the position of the open file description.
  export
  pwrite : ToBuf r => r -> OffT -> EPrim Bits32
  pwrite v off =
    case unsafeToBuf v of
      Left (CP sz ptr)        =>
        toSize $ prim__pwriteptr (fileDesc fd) ptr 0 sz off
      Right (BS n $ BV b o _) =>
        toSize $ prim__pwrite (fileDesc fd) (unsafeGetBuffer b) (cast o) (cast n) off

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
  getFlags t =
   let r # t := toF1 (prim__getFlags (fileDesc fd)) t
    in if r < 0 then E (inject $ fromNeg r) t else R (F $ cast r) t

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
mkstemp f t =
  let pat     := "\{f}XXXXXX"
      len     := cast {to = Bits32} $ stringByteLength pat
      buf # t := toF1 (prim__newBuf len) t
      _   # t := ioToF1 (setString buf 0 pat) t
      R fd  t := toFD (prim__mkstemp buf) t | E x t => E x t
      nm  # t := fromBuf (B len buf) t
   in R (fd, nm) t

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
readlink : FromBuf a => (file : String) -> EPrim a
readlink f = allocRead 4096 $ prim__readlink f

--------------------------------------------------------------------------------
-- Standard input and output
--------------------------------------------------------------------------------

export %inline
stdout : String -> PrimIO ()
stdout s = Errno.ignore $ fwrite {es = [Errno]} Stdout s

export %inline
stdoutLn : String -> PrimIO ()
stdoutLn = stdout . (++ "\n")

export %inline
prnt : Show a => a -> PrimIO ()
prnt = stdout . show

export %inline
prntLn : Show a => a -> PrimIO ()
prntLn = stdoutLn . show

export %inline
stderr : String -> PrimIO ()
stderr s = ignore $ fwrite {es = [Errno]} Stderr s

export %inline
stderrLn : String -> PrimIO ()
stderrLn = stderr . (++ "\n")
