module System.Posix.File

import Data.Bits

import Derive.Prelude

import public Data.Buffer
import public Data.Buffer.Core
import public Data.ByteString
import public Data.ByteVect

import public Data.C.Integer

import public System.Posix.Errno
import public System.Posix.File.Flags
import public System.Posix.File.Whence

%default total
%language ElabReflection
%hide Language.Reflection.TTImp.Mode

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_open, posix-idris"
prim__open : String -> CInt -> ModeT -> PrimIO CInt

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

%foreign "C:li_pwrite, posix-idris"
prim__pwrite : (file : Bits32) -> Buffer -> (off,max : Bits32) -> OffT -> PrimIO SsizeT

%foreign "C:lseek, posix-idris"
prim__lseek : (file : Bits32) -> (off : OffT) -> (whence : CInt) -> PrimIO OffT

%foreign "C:li_set_flags, posix-idris"
prim__setFlags : (file : Bits32) -> (flags : CInt) -> PrimIO CInt

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
-- FileDesc
--------------------------------------------------------------------------------

||| A wrapper around a file descriptor.
public export
record Fd where
  constructor MkFd
  fd : Bits32

%name Fd fd

%runElab derive "Fd" [Show,Eq,Ord]

public export
0 FileDesc : Type -> Type
FileDesc a = Cast a Fd

export %inline
Cast Bits32 Fd where cast = MkFd

export %inline
fileDesc : FileDesc a => a -> Bits32
fileDesc = fd . cast

||| Standard input and output file descriptors
public export
data StdIO : Type where
  Stdin  : StdIO
  Stdout : StdIO
  Stderr : StdIO

%runElab derive "StdIO" [Show,Eq,Ord]

export %inline
Cast StdIO Fd where
  cast = MkFd . cast . conIndexStdIO

--------------------------------------------------------------------------------
-- Mode
--------------------------------------------------------------------------------

||| File permissions.
public export
record Mode where
  constructor M
  mode : ModeT

%runElab derive "Mode" [Show,Eq,Ord,FromInteger]

public export
Semigroup Mode where
  M x <+> M y = M $ x .|. y

public export
Monoid Mode where neutral = M 0

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

||| Converts a number of bytes read into a buffer to a `ByteString`
export %inline
toBytes :
     Bits32
  -> (Buffer -> Bits32 -> PrimIO SsizeT)
  -> IO (Either Errno ByteString)
toBytes n act =
  fromPrim $ \w =>
    let MkIORes buf w := prim__newBuf n w
        MkIORes rd  w := act buf n w
     in case rd < 0 of
          False => MkIORes (Right $ unsafeByteString (cast rd) buf) w
          True  => MkIORes (Left $ fromNeg rd) w

export %inline
toFD : PrimIO CInt -> IO (Either Errno Fd)
toFD = toVal (MkFd . cast)

--------------------------------------------------------------------------------
-- File Operations
--------------------------------------------------------------------------------

||| Tries to open a file with the given flags and mode.
export %inline
openFile : String -> Flags -> Mode -> IO (Either Errno Fd)
openFile p (F f) (M m) = toFD (prim__open p f m)

parameters {auto fid : FileDesc a}
           (fd       : a)

  ||| Closes a file descriptor.
  export %inline
  close : IO (Either Errno ())
  close = toUnit (prim__close $ fileDesc fd)

  ||| Reads at most `n` bytes from a file into an allocated pointer.
  export %inline
  readPtr : AnyPtr -> (n : Bits32) -> IO (Either Errno Bits32)
  readPtr ptr n = toSize $ prim__readptr (fileDesc fd) ptr n

  ||| Reads at most `n` bytes from a file into a buffer.
  export %inline
  readRaw : Buffer -> (n : Bits32) -> IO (Either Errno Bits32)
  readRaw buf n = toSize $ prim__read (fileDesc fd) buf n

  ||| Reads at most `n` bytes from a file into a bytestring.
  export
  read : (n : Bits32) -> IO (Either Errno ByteString)
  read n = toBytes n $  prim__read (fileDesc fd)

  ||| Atomically reads up to `n` bytes from the given file at
  ||| the given file offset.
  |||
  ||| Notes: This will only work with seekable files but not with
  |||        arbitrary data streams such as pipes or sockets.
  |||        Also, it will not change the position of the open file description.
  export
  pread : (n : Bits32) -> OffT -> IO (Either Errno ByteString)
  pread n off = toBytes n $ \b,x => prim__pread (fileDesc fd) b x off

  ||| Writes up to the number of bytes in the bytestring
  ||| to the given file.
  |||
  ||| Note: This is an atomic operation if `fd` is a regular file that
  |||       was opened in "append" mode (with the `O_APPEND` flag).
  export
  writeBytes : ByteString -> IO (Either Errno Bits32)
  writeBytes (BS n $ BV b o _) =
    toSize $ prim__write (fileDesc fd) (unsafeGetBuffer b) (cast o) (cast n)

  ||| Reads at most `n` bytes from a file into a bytestring.
  export %inline
  writeRaw : Buffer -> (offset,n : Bits32) -> IO (Either Errno Bits32)
  writeRaw buf o n = toSize $ prim__write (fileDesc fd) buf o n


  ||| Atomically writes up to the number of bytes in the bytestring
  ||| to the given file at the given file offset.
  |||
  ||| Notes: This will only work with seekable files but not with
  |||        arbitrary data streams such as pipes or sockets.
  |||        Also, it will not change the position of the open file description.
  export
  pwriteBytes : ByteString -> OffT -> IO (Either Errno Bits32)
  pwriteBytes (BS n $ BV b o _) off =
    toSize $ prim__pwrite (fileDesc fd) (unsafeGetBuffer b) (cast o) (cast n) off

  export %inline
  write : {n : _} -> IBuffer n -> IO (Either Errno Bits32)
  write ibuf = writeBytes (fromIBuffer ibuf)

  export %inline
  writeStr : String -> IO (Either Errno Bits32)
  writeStr = writeBytes . fromString

  export %inline
  writeStrLn : String -> IO (Either Errno Bits32)
  writeStrLn = writeStr . (++ "\n")

--------------------------------------------------------------------------------
-- File seeking
--------------------------------------------------------------------------------

  ||| Moves the file pointer to the given offset relative to the
  ||| `Whence` value.
  export %inline
  lseek : HasIO io => OffT -> Whence -> io OffT
  lseek offset whence =
    primIO $ prim__lseek (fileDesc fd) offset (cast $ whenceCode whence)

--------------------------------------------------------------------------------
-- Duplicating file descriptors
--------------------------------------------------------------------------------

  ||| Duplicates the given open file descriptor.
  |||
  ||| The duplicate is guaranteed to be given the smallest available
  ||| file descriptor.
  export %inline
  dup : IO (Either Errno Fd)
  dup = toFD $ prim__dup (fileDesc fd)

  ||| Duplicates the given open file descriptor.
  |||
  ||| The new file descriptor vill have the integer value of `fd2`.
  ||| This is an atomic operation that will close `fd2` if it is still open.
  export %inline
  dup2 : FileDesc b => (fd2 : b) -> IO (Either Errno Fd)
  dup2 fd2 = toFD $ prim__dup2 (fileDesc fd) (fileDesc fd2)

  ||| Duplicates the given open file descriptor.
  |||
  ||| The new file descriptor vill have the integer value of `fd2`.
  ||| This is an atomic operation that will close `fd2` if it is still open.
  export %inline
  dupfd : (start : Bits32) -> IO (Either Errno Fd)
  dupfd fd2 = toFD $ prim__dupfd (fileDesc fd) fd2

--------------------------------------------------------------------------------
-- Setting and getting file flags
--------------------------------------------------------------------------------

  ||| Gets the flags set at an open file descriptor.
  export
  getFlags : IO (Either Errno Flags)
  getFlags  =
    fromPrim $ \w =>
      let MkIORes r w := prim__getFlags (fileDesc fd) w
       in case r < 0 of
            True  => MkIORes (negErr r) w
            False => MkIORes (Right $ F r) w

  ||| Sets the flags of an open file descriptor.
  |||
  ||| Note: This replaces the currently set flags. See also `addFlags`.
  export %inline
  setFlags : Flags -> IO (Either Errno ())
  setFlags (F fs) = toUnit $ prim__setFlags (fileDesc fd) fs

  ||| Adds the given flags to the flags set for an open
  ||| file descriptor by ORing them with the currently set flags.
  export
  addFlags : Flags -> IO (Either Errno ())
  addFlags fs =
    getFlags >>= \case
      Right x => setFlags (x <+> fs)
      Left  x => pure (Left x)

  ||| Truncates a file to the given length.
  export %inline
  ftruncate : OffT -> IO (Either Errno ())
  ftruncate len = toUnit $ prim__ftruncate (fileDesc fd) len

||| Truncates a file to the given length.
export %inline
truncate : String -> OffT -> IO (Either Errno ())
truncate f len = toUnit $ prim__truncate f len

||| Atomically creates and opens a temporary, unique file.
export
mkstemp : String -> IO (Either Errno (Fd, String))
mkstemp f =
  let pat := "\{f}XXXXXX"
      len := stringByteLength pat
   in do
        buf <- fromPrim $ prim__newBuf (cast len)
        setString buf 0 pat
        Right fd <- toFD (prim__mkstemp buf) | Left x => pure (Left x)
        str <- getString buf 0 len
        pure $ Right (fd, str)

--------------------------------------------------------------------------------
-- Links
--------------------------------------------------------------------------------

||| Creates a (hard) link to a file.
export %inline
link : (file, link : String) -> IO (Either Errno ())
link f l = toUnit $ prim__link f l

||| Creates a (hard) link to a file.
export %inline
symlink : (file, link : String) -> IO (Either Errno ())
symlink f l = toUnit $ prim__symlink f l

||| Deletes a (hard) link to a file.
|||
||| If this is the last link to the file, the file is removed.
|||
||| Note: Files with open file descriptors will only be deleted after the last
|||       open file descriptor is closed, but the file name will already
|||       disapper from the file system before that.
export %inline
unlink : (file : String) -> IO (Either Errno ())
unlink f = toUnit $ prim__unlink f

||| Removes a file or (empty) directory calling `unlink` or `rmdir`
||| internally.
export %inline
remove : (file : String) -> IO (Either Errno ())
remove f = toUnit $ prim__remove f

||| Renames a file within a file system.
|||
||| Note: This will fail if the two paths point to different file systems.
|||       In that case, the file needs to be copied from one FS to the other.
export %inline
rename : (file, link : String) -> IO (Either Errno ())
rename f l = toUnit $ prim__rename f l

||| Returns the path of a file a symbolic link points to
|||
||| This allocates a buffer of 4096 bytes for the byte array holding
||| the result.
export %inline
readlink : (file : String) -> IO (Either Errno ByteString)
readlink f = toBytes 4096 $ prim__readlink f

--------------------------------------------------------------------------------
-- Standard input and output
--------------------------------------------------------------------------------

export %inline
stdout : HasIO io => String -> io ()
stdout = liftIO . ignore . writeStr Stdout

export %inline
stdoutLn : HasIO io => String -> io ()
stdoutLn = liftIO . ignore . writeStrLn Stdout
