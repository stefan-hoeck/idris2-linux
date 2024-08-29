module System.Linux.File

import Data.Bits
import Data.Buffer
import Data.C.Integer

import public Data.Buffer.Core
import public Data.ByteString
import public Data.ByteVect
import public Data.FilePath

import Derive.Finite
import Derive.Prelude

import public System.Linux.Error
import public System.Linux.File.Flags
import public System.Linux.File.Whence

%default total
%language ElabReflection
%hide Language.Reflection.TTImp.Mode

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_open, linux-idris"
prim__open : String -> CInt -> ModeT -> PrimIO CInt

%foreign "C:li_close, linux-idris"
prim__close : Bits32 -> PrimIO CInt

%foreign "C__collect_safe:li_read, linux-idris"
prim__read : (file : Bits32) -> Buffer -> (max : Bits32) -> PrimIO SsizeT

%foreign "C__collect_safe:li_pread, linux-idris"
prim__pread : (file : Bits32) -> Buffer -> (max : Bits32) -> OffT -> PrimIO SsizeT

%foreign "C__collect_safe:li_write, linux-idris"
prim__write : (file : Bits32) -> Buffer -> (off,max : Bits32) -> PrimIO SsizeT

%foreign "C__collect_safe:li_pwrite, linux-idris"
prim__pwrite : (file : Bits32) -> Buffer -> (off,max : Bits32) -> OffT -> PrimIO SsizeT

%foreign "C:lseek, linux-idris"
prim__lseek : (file : Bits32) -> (off : OffT) -> (whence : CInt) -> PrimIO OffT

%foreign "C:li_set_flags, linux-idris"
prim__setFlags : (file : Bits32) -> (flags : CInt) -> PrimIO CInt

%foreign "C:li_get_flags, linux-idris"
prim__getFlags : (file : Bits32) -> PrimIO CInt

%foreign "C:li_dup, linux-idris"
prim__dup : (file : Bits32) -> PrimIO CInt

%foreign "C:li_dup2, linux-idris"
prim__dup2 : (file, dst : Bits32) -> PrimIO CInt

%foreign "C:li_dupfd, linux-idris"
prim__dupfd : (file, startfd : Bits32) -> PrimIO CInt

%foreign "C:li_ftruncate, linux-idris"
prim__ftruncate : (file : Bits32) -> (len : OffT) -> PrimIO CInt

%foreign "C:li_truncate, linux-idris"
prim__truncate : (file : String) -> (len : OffT) -> PrimIO CInt

%foreign "C:li_mkstemp, linux-idris"
prim__mkstemp : Buffer -> PrimIO CInt

--------------------------------------------------------------------------------
-- FileDesc
--------------------------------------------------------------------------------

||| Interface for types describing file descriptors
public export
interface FileDesc a where
  fileDesc : a -> Bits32

export %inline
FileDesc Bits32 where fileDesc x = x

public export
data StdIO : Type where
  Stdin  : StdIO
  Stdout : StdIO
  Stderr : StdIO

%runElab derive "StdIO" [Show,Eq,Ord]

export %inline
FileDesc StdIO where
  fileDesc = cast . conIndexStdIO

--------------------------------------------------------------------------------
-- FileError
--------------------------------------------------------------------------------

public export
data FileErr : Type where
  OpenErr  : FilePath -> Error -> FileErr
  CloseErr : Error -> FileErr
  ReadErr  : Error -> FileErr
  WriteErr : Error -> FileErr
  FlagsErr : Error -> FileErr
  DupErr   : Error -> FileErr
  FilErr   : Error -> FileErr

%runElab derive "FileErr" [Show,Eq]

export
Interpolation FileErr where
  interpolate (OpenErr p x) = "Error when opening \{p}: \{x}"
  interpolate (CloseErr x)  = "Error when closing file descriptor: \{x}"
  interpolate (ReadErr x)   = "Error when reading from file descriptor: \{x}"
  interpolate (WriteErr x)  = "Error when writing to file descriptor: \{x}"
  interpolate (FlagsErr x)  = "Error when setting/getting file descriptor flags: \{x}"
  interpolate (DupErr x)    = "Error when duplicating file descriptor: \{x}"
  interpolate (FilErr x)    = "File error: \{x}"

--------------------------------------------------------------------------------
-- Mode
--------------------------------------------------------------------------------

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
-- Results
--------------------------------------------------------------------------------

public export
data ReadRes : Type where
  EOF    : ReadRes
  RAgain : ReadRes
  Bytes  : ByteString -> ReadRes

%runElab derive "ReadRes" [Show]

public export
data WriteRes : Type where
  WAgain  : WriteRes
  Written : (n : Nat) -> WriteRes

%runElab derive "WriteRes" [Show]

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

toReadRes : PrimIO (Buffer,SsizeT) -> IO (Either FileErr ReadRes)
toReadRes act =
  fromPrim $ \w =>
    let MkIORes (buf,rd) w := act w
     in case rd of
          0 => MkIORes (Right EOF) w
          x => case x < 0 of
            False => MkIORes (Right $ Bytes $ unsafeByteString (cast x) buf) w
            True  => case fromRes x of
              EAGAIN => MkIORes (Right RAgain) w
              x      => MkIORes (Left $ ReadErr x) w

toWriteRes : PrimIO SsizeT -> IO (Either FileErr WriteRes)
toWriteRes act =
  fromPrim $ \w =>
    let MkIORes r w := act w
     in case r < 0 of
          True => case fromRes r of
            EAGAIN => MkIORes (Right WAgain) w
            x      => MkIORes (Left $ WriteErr x) w
          False => MkIORes (Right $ Written (cast r)) w

--------------------------------------------------------------------------------
-- File Operations
--------------------------------------------------------------------------------

||| Flags for creating a file for output.
export
create : Flags
create = O_WRONLY <+> O_CREAT <+> O_TRUNC

||| Flags for creating a file for output.
|||
||| If the file exists, data is appended to it.
export
append : Flags
append = O_WRONLY <+> O_CREAT <+> O_APPEND

||| Tries to open a file with the given flags and mode.
export %inline
openFile : FilePath -> Flags -> Mode -> IO (Either FileErr Bits32)
openFile p (F f) (M m) = toFD (OpenErr p) ( prim__open (interpolate p) f m)

||| Closes a file descriptor.
export %inline
close : FileDesc a => a -> IO (Either FileErr ())
close fd = toUnit CloseErr (prim__close (fileDesc fd))

||| Reads at most `n` bytes from a file into a bytestring.
export %inline
readRaw : FileDesc a => a -> Buffer -> (n : Bits32) -> IO (Either FileErr Bits32)
readRaw fd buf n = toSize ReadErr $ prim__read (fileDesc fd) buf n

||| Reads at most `n` bytes from a file into a bytestring.
export
read : FileDesc a => a -> (n : Bits32) -> IO (Either FileErr ReadRes)
read fd n =
  toReadRes $ \w =>
    let MkIORes buf w := prim__newBuf n w
        MkIORes rd  w := prim__read (fileDesc fd) buf n w
     in MkIORes (buf,rd) w

||| Atomically reads up to `n` bytes from the given file at
||| the given file offset.
|||
||| Notes: This will only work with seekable files but not with
|||        arbitrary data streams such as pipes or sockets.
|||        Also, it will not change the position of the open file description.
export
pread : FileDesc a => a -> (n : Bits32) -> OffT -> IO (Either FileErr ReadRes)
pread fd n off =
  toReadRes $ \w =>
    let MkIORes buf w := prim__newBuf n w
        MkIORes rd  w := prim__pread (fileDesc fd) buf n off w
     in MkIORes (buf,rd) w

||| Writes up to the number of bytes in the bytestring
||| to the given file.
|||
||| Note: This is an atomic operation if `fd` is a regular file that
|||       was opened in "append" mode (with the `O_APPEND` flag).
export
writeBytes :
     {auto fid : FileDesc a}
  -> (fd : a)
  -> ByteString
  -> IO (Either FileErr WriteRes)
writeBytes fd (BS n $ BV b o _) =
  toWriteRes $ prim__write (fileDesc fd) (unsafeGetBuffer b) (cast o) (cast n)

||| Reads at most `n` bytes from a file into a bytestring.
export %inline
writeRaw : FileDesc a => a -> Buffer -> (offset,n : Bits32) -> IO (Either FileErr Bits32)
writeRaw fd buf o n = toSize ReadErr $ prim__write (fileDesc fd) buf o n


||| Atomically writes up to the number of bytes in the bytestring
||| to the given file at the given file offset.
|||
||| Notes: This will only work with seekable files but not with
|||        arbitrary data streams such as pipes or sockets.
|||        Also, it will not change the position of the open file description.
export
pwriteBytes :
     {auto fid : FileDesc a}
  -> a
  -> ByteString
  -> OffT
  -> IO (Either FileErr WriteRes)
pwriteBytes fd (BS n $ BV b o _) off =
  toWriteRes $ prim__pwrite (fileDesc fd) (unsafeGetBuffer b) (cast o) (cast n) off

export %inline
write : {n : _} -> FileDesc a => a -> IBuffer n -> IO (Either FileErr WriteRes)
write fd ibuf = writeBytes fd (fromIBuffer ibuf)

export %inline
writeStr : FileDesc a => a -> String -> IO (Either FileErr WriteRes)
writeStr fd = writeBytes fd . fromString

--------------------------------------------------------------------------------
-- File seeking
--------------------------------------------------------------------------------

||| Moves the file pointer to the given offset relative to the
||| `Whence` value.
export %inline
lseek : HasIO io => FileDesc a => a -> OffT -> Whence -> io OffT
lseek fd offset whence =
  primIO $ prim__lseek (fileDesc fd) offset (cast $ whenceCode whence)

--------------------------------------------------------------------------------
-- Setting and getting file flags
--------------------------------------------------------------------------------

||| Gets the flags set at an open file descriptor.
export
getFlags : FileDesc a => a -> IO (Either FileErr Flags)
getFlags fd =
  fromPrim $ \w =>
    let MkIORes r w := prim__getFlags (fileDesc fd) w
     in case r < 0 of
          True  => MkIORes (resErr r FlagsErr) w
          False => MkIORes (Right $ F r) w

||| Sets the flags of an open file descriptor.
|||
||| Note: This replaces the currently set flags. See also `addFlags`.
export %inline
setFlags : FileDesc a => a -> Flags -> IO (Either FileErr ())
setFlags fd (F fs) = toUnit FlagsErr $ prim__setFlags (fileDesc fd) fs

||| Adds the given flags to the flags set for an open
||| file descriptor by ORing them with the currently set flags.
export
addFlags : FileDesc a => a -> Flags -> IO (Either FileErr ())
addFlags fd fs = do
  Right x <- getFlags fd | Left err => pure (Left err)
  setFlags fd (x <+> fs)

||| Truncates a file to the given length.
export %inline
ftruncate : FileDesc a => a -> OffT -> IO (Either FileErr ())
ftruncate fd len = toUnit FilErr $ prim__ftruncate (fileDesc fd) len

||| Truncates a file to the given length.
export %inline
truncate : String -> OffT -> IO (Either FileErr ())
truncate f len = toUnit FilErr $ prim__truncate f len

||| Atomically creates and opens a temporary, unique file.
export
mkstemp : FilePath -> IO (Either FileErr (Bits32, String))
mkstemp f =
  let pat := "\{f}XXXXXX"
      len := stringByteLength pat
   in do
        buf <- fromPrim $ prim__newBuf (cast len)
        setString buf 0 pat
        Right fd <- toFD (OpenErr f) (prim__mkstemp buf)
          | Left x => pure (Left x)
        str <- getString buf 0 len
        pure $ Right (fd, str)

--------------------------------------------------------------------------------
-- Duplicating file descriptors
--------------------------------------------------------------------------------

||| Duplicates the given open file descriptor.
|||
||| The duplicate is guaranteed to be given the smallest available
||| file descriptor.
export %inline
dup : FileDesc a => a -> IO (Either FileErr Bits32)
dup fd = toFD DupErr $ prim__dup (fileDesc fd)

||| Duplicates the given open file descriptor.
|||
||| The new file descriptor vill have the integer value of `fd2`.
||| This is an atomic operation that will close `fd2` if it is still open.
export %inline
dup2 : FileDesc a => FileDesc b => a -> (fd2 : b) -> IO (Either FileErr Bits32)
dup2 fd fd2 = toFD DupErr $ prim__dup2 (fileDesc fd) (fileDesc fd2)

||| Duplicates the given open file descriptor.
|||
||| The new file descriptor vill have the integer value of `fd2`.
||| This is an atomic operation that will close `fd2` if it is still open.
export %inline
dupfd : FileDesc a => a -> (start : Bits32) -> IO (Either FileErr Bits32)
dupfd fd fd2 = toFD DupErr $ prim__dupfd (fileDesc fd) fd2
