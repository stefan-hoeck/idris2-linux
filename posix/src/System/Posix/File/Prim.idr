module System.Posix.File

import Data.Bits

import Derive.Prelude

import public Data.Buffer
import public Data.Buffer.Core
import public Data.ByteString
import public Data.ByteVect

import public Data.C.Ptr

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

public export %inline
SizeOf Fd where
  sizeof_ = sizeof Bits32

export %inline
Deref Fd where
  deref p = MkFd <$> deref p

export %inline
SetPtr Fd where
  setPtr p = setPtr p . fd

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
-- Utilities
--------------------------------------------------------------------------------

||| Converts a number of bytes read into a buffer to a `ByteString`
export %inline
toBytes :
     Bits32
  -> (Buffer -> Bits32 -> PrimIO SsizeT)
  -> PrimIO (Either Errno ByteString)
toBytes n act w =
  let MkIORes buf w := prim__newBuf n w
      MkIORes rd  w := act buf n w
   in if rd < 0
         then MkIORes (Left $ fromNeg rd) w
         else MkIORes (Right $ unsafeByteString (cast rd) buf) w

export %inline
toFD : PrimIO CInt -> PrimIO (Either Errno Fd)
toFD = toVal (MkFd . cast)

--------------------------------------------------------------------------------
-- File Operations
--------------------------------------------------------------------------------

||| Tries to open a file with the given flags and mode.
export %inline
openFile : String -> Flags -> Mode -> PrimIO (Either Errno Fd)
openFile p (F f) (M m) = toFD (prim__open p f m)

parameters {auto fid : FileDesc a}
           (fd       : a)

  ||| Closes a file descriptor.
  export %inline
  close : PrimIO (Either Errno ())
  close = toUnit (prim__close $ fileDesc fd)

  ||| Reads at most `n` bytes from a file into an allocated pointer.
  export %inline
  readPtr : AnyPtr -> (n : Bits32) -> PrimIO (Either Errno Bits32)
  readPtr ptr n = toSize $ prim__readptr (fileDesc fd) ptr n

  ||| Reads at most `n * sizeof a` bytes into a preallocated array.
  export
  readArr :
       {n : _}
    -> {auto sof : SizeOf b}
    -> CArrayIO n b
    -> PrimIO (Either Errno (k ** CArrayIO k b))
  readArr p w =
    let ptr                  := unsafeUnwrap p
        sz                   := sizeof b
        MkIORes (Right bs) w := readPtr ptr (cast n * sz) w
          | MkIORes (Left x) w => MkIORes (Left x) w
        k                    := cast (bs `div` sz)
     in MkIORes (Right (k ** unsafeWrap ptr)) w

  ||| Reads at most `n * sizeof a` bytes into a preallocated array and
  ||| converts it to a list of values.
  export
  readVals :
       {n : _}
    -> {auto sof : SizeOf b}
    -> {auto der : Deref b}
    -> CArrayIO n b
    -> (b -> PrimIO c)
    -> PrimIO (Either Errno $ List c)
  readVals p f w =
    let MkIORes (Right (k ** arr)) w := readArr p w
          | MkIORes (Left x) w => MkIORes (Left x) w
        MkIORes vs w           := values [] arr f k w
     in MkIORes (Right vs) w

  ||| Reads at most `n` bytes from a file into a buffer.
  export %inline
  readRaw : Buffer -> (n : Bits32) -> PrimIO (Either Errno Bits32)
  readRaw buf n = toSize $ prim__read (fileDesc fd) buf n

  ||| Reads at most `n` bytes from a file into a bytestring.
  export
  read : (n : Bits32) -> PrimIO (Either Errno ByteString)
  read n = toBytes n $  prim__read (fileDesc fd)

  ||| Atomically reads up to `n` bytes from the given file at
  ||| the given file offset.
  |||
  ||| Notes: This will only work with seekable files but not with
  |||        arbitrary data streams such as pipes or sockets.
  |||        Also, it will not change the position of the open file description.
  export
  pread : (n : Bits32) -> OffT -> PrimIO (Either Errno ByteString)
  pread n off = toBytes n $ \b,x => prim__pread (fileDesc fd) b x off

  ||| Writes up to the number of bytes in the bytestring
  ||| to the given file.
  |||
  ||| Note: This is an atomic operation if `fd` is a regular file that
  |||       was opened in "append" mode (with the `O_APPEND` flag).
  export
  writeBytes : ByteString -> PrimIO (Either Errno Bits32)
  writeBytes (BS n $ BV b o _) =
    toSize $ prim__write (fileDesc fd) (unsafeGetBuffer b) (cast o) (cast n)

  ||| Writes up to the given number of bytes from the given buffer starting
  ||| at the given offset.
  |||
  ||| Note: This is an atomic operation if `fd` is a regular file that
  |||       was opened in "append" mode (with the `O_APPEND` flag).
  export %inline
  writeRaw : Buffer -> (offset,n : Bits32) -> PrimIO (Either Errno Bits32)
  writeRaw buf o n = toSize $ prim__write (fileDesc fd) buf o n

  ||| Writes up to the number of bytes from the given C ptr.
  |||
  ||| Note: This is an atomic operation if `fd` is a regular file that
  |||       was opened in "append" mode (with the `O_APPEND` flag).
  export %inline
  writePtr : AnyPtr -> (n : Bits32) -> PrimIO (Either Errno Bits32)
  writePtr buf n = toSize $ prim__writeptr (fileDesc fd) buf 0 n

  ||| Writes the content of the given array.
  |||
  ||| Note: This is an atomic operation if `fd` is a regular file that
  |||       was opened in "append" mode (with the `O_APPEND` flag).
  export %inline
  writeArr : {n : _} -> SizeOf b => CArrayIO n b -> PrimIO (Either Errno Bits32)
  writeArr p = writePtr (unsafeUnwrap p) (cast n * sizeof b)


  ||| Atomically writes up to the number of bytes in the bytestring
  ||| to the given file at the given file offset.
  |||
  ||| Notes: This will only work with seekable files but not with
  |||        arbitrary data streams such as pipes or sockets.
  |||        Also, it will not change the position of the open file description.
  export
  pwriteBytes : ByteString -> OffT -> PrimIO (Either Errno Bits32)
  pwriteBytes (BS n $ BV b o _) off =
    toSize $ prim__pwrite (fileDesc fd) (unsafeGetBuffer b) (cast o) (cast n) off

  export %inline
  write : {n : _} -> IBuffer n -> PrimIO (Either Errno Bits32)
  write ibuf = writeBytes (fromIBuffer ibuf)

  export %inline
  writeStr : String -> PrimIO (Either Errno Bits32)
  writeStr = writeBytes . fromString

  export %inline
  writeStrLn : String -> PrimIO (Either Errno Bits32)
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
  dup : PrimIO (Either Errno Fd)
  dup = toFD $ prim__dup (fileDesc fd)

  ||| Duplicates the given open file descriptor.
  |||
  ||| The new file descriptor vill have the integer value of `fd2`.
  ||| This is an atomic operation that will close `fd2` if it is still open.
  export %inline
  dup2 : FileDesc b => (fd2 : b) -> PrimIO (Either Errno Fd)
  dup2 fd2 = toFD $ prim__dup2 (fileDesc fd) (fileDesc fd2)

  ||| Duplicates the given open file descriptor.
  |||
  ||| The new file descriptor vill have the integer value of `fd2`.
  ||| This is an atomic operation that will close `fd2` if it is still open.
  export %inline
  dupfd : (start : Bits32) -> PrimIO (Either Errno Fd)
  dupfd fd2 = toFD $ prim__dupfd (fileDesc fd) fd2

--------------------------------------------------------------------------------
-- Setting and getting file flags
--------------------------------------------------------------------------------

  ||| Gets the flags set at an open file descriptor.
  export
  getFlags : PrimIO (Either Errno Flags)
  getFlags w =
   let MkIORes r w := prim__getFlags (fileDesc fd) w
    in MkIORes (if r < 0 then Left (fromNeg r) else Right (F $ cast r)) w

  ||| Sets the flags of an open file descriptor.
  |||
  ||| Note: This replaces the currently set flags. See also `addFlags`.
  export %inline
  setFlags : Flags -> PrimIO (Either Errno ())
  setFlags (F fs) = toUnit $ prim__setFlags (fileDesc fd) fs

  ||| Adds the given flags to the flags set for an open
  ||| file descriptor by ORing them with the currently set flags.
  export
  addFlags : Flags -> PrimIO (Either Errno ())
  addFlags fs w =
    let MkIORes (Right x) w := getFlags w | MkIORes (Left x) w => MkIORes (Left x) w
     in setFlags (x <+> fs) w

  ||| Truncates a file to the given length.
  export %inline
  ftruncate : OffT -> PrimIO (Either Errno ())
  ftruncate len = toUnit $ prim__ftruncate (fileDesc fd) len

||| Truncates a file to the given length.
export %inline
truncate : String -> OffT -> PrimIO (Either Errno ())
truncate f len = toUnit $ prim__truncate f len

||| Atomically creates and opens a temporary, unique file.
export
mkstemp : String -> PrimIO (Either Errno (Fd, String))
mkstemp f w =
  let pat := "\{f}XXXXXX"
      len := stringByteLength pat
      MkIORes buf w := prim__newBuf (cast len) w
      MkIORes _ w   := toPrim (setString buf 0 pat) w
      MkIORes (Right fd) w := toFD (prim__mkstemp buf) w
        | MkIORes (Left x) w => MkIORes (Left x) w
      MkIORes str w :=  toPrim (getString buf 0 len) w
   in MkIORes (Right (fd, str)) w

--------------------------------------------------------------------------------
-- Links
--------------------------------------------------------------------------------

||| Creates a (hard) link to a file.
export %inline
link : (file, link : String) -> PrimIO (Either Errno ())
link f l = toUnit $ prim__link f l

||| Creates a (hard) link to a file.
export %inline
symlink : (file, link : String) -> PrimIO (Either Errno ())
symlink f l = toUnit $ prim__symlink f l

||| Deletes a (hard) link to a file.
|||
||| If this is the last link to the file, the file is removed.
|||
||| Note: Files with open file descriptors will only be deleted after the last
|||       open file descriptor is closed, but the file name will already
|||       disapper from the file system before that.
export %inline
unlink : (file : String) -> PrimIO (Either Errno ())
unlink f = toUnit $ prim__unlink f

||| Removes a file or (empty) directory calling `unlink` or `rmdir`
||| internally.
export %inline
remove : (file : String) -> PrimIO (Either Errno ())
remove f = toUnit $ prim__remove f

||| Renames a file within a file system.
|||
||| Note: This will fail if the two paths point to different file systems.
|||       In that case, the file needs to be copied from one FS to the other.
export %inline
rename : (file, link : String) -> PrimIO (Either Errno ())
rename f l = toUnit $ prim__rename f l

||| Returns the path of a file a symbolic link points to
|||
||| This allocates a buffer of 4096 bytes for the byte array holding
||| the result.
export %inline
readlink : (file : String) -> PrimIO (Either Errno ByteString)
readlink f = toBytes 4096 $ prim__readlink f

--------------------------------------------------------------------------------
-- Standard input and output
--------------------------------------------------------------------------------

parameters {auto hio : HasIO io}

  export %inline
  stdout : String -> io ()
  stdout s = ignore $ primIO (writeStr Stdout s)

  export %inline
  stdoutLn : String -> io ()
  stdoutLn s = ignore $ primIO (writeStrLn Stdout s)

  export %inline
  prnt : Show a => a -> io ()
  prnt = stdout . show

  export %inline
  prntLn : Show a => a -> io ()
  prntLn = stdoutLn . show

  export %inline
  stderr : String -> io ()
  stderr s = ignore $ primIO (writeStr Stderr s)

  export %inline
  stderrLn : String -> io ()
  stderrLn s = ignore $ primIO (writeStrLn Stderr s)
