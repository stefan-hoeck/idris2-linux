module System.Linux.File

import Data.Bits
import Data.Buffer
import Data.Buffer.Core
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

%foreign "C__collect_safe:li_write, linux-idris"
prim__write : (file : Bits32) -> Buffer -> (off,max : Bits32) -> PrimIO SsizeT

%foreign "C:lseek, linux-idris"
prim__lseek : (file : Bits32) -> (off : OffT) -> (whence : CInt) -> PrimIO OffT

%foreign "C:li_set_flags, linux-idris"
prim__setFlags : (file : Bits32) -> (flags : CInt) -> PrimIO CInt

%foreign "C:li_get_flags, linux-idris"
prim__getFlags : (file : Bits32) -> PrimIO CInt

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

%runElab derive "FileErr" [Show,Eq]

export
Interpolation FileErr where
  interpolate (OpenErr p x) = "Error when opening \{p}: \{x}"
  interpolate (CloseErr x)  = "Error when closing file descriptor: \{x}"
  interpolate (ReadErr x)   = "Error when reading from file descriptor: \{x}"
  interpolate (WriteErr x)  = "Error when writing to file descriptor: \{x}"
  interpolate (FlagsErr x)  = "Error when setting/getting file descriptor flags: \{x}"

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
openFile pth (F f) (M m) =
  fromPrim $ \w =>
    let MkIORes r w := prim__open (interpolate pth) f m w
     in case r < 0 of
          True  => MkIORes (resErr r $ OpenErr pth) w
          False => MkIORes (Right $ cast r) w

||| Closes a file descriptor.
export %inline
close : FileDesc a => a -> IO (Either FileErr ())
close fd =
  fromPrim $ \w =>
    let MkIORes r w := prim__close (fileDesc fd) w
     in case r < 0 of
          True  => MkIORes (resErr r CloseErr) w
          False => MkIORes (Right ()) w

public export
data ReadRes : Type where
  EOF   : ReadRes
  Again : ReadRes
  Bytes : ByteString -> ReadRes

%runElab derive "ReadRes" [Show]

export
read : FileDesc a => a -> (n : Bits32) -> IO (Either FileErr ReadRes)
read fd n =
  fromPrim $ \w =>
    let MkIORes buf w := prim__newBuf n w
        MkIORes rd  w := prim__read (fileDesc fd) buf n w
     in case rd of
          0 => MkIORes (Right EOF) w
          x => case x < 0 of
            False => MkIORes (Right $ Bytes $ unsafeByteString (cast x) buf) w
            True  => case fromRes x of
              EAGAIN => MkIORes (Right Again) w
              x      => MkIORes (Left $ ReadErr x) w

public export
data WriteRes : Type where
  WAgain  : WriteRes
  Written : (n : Nat) -> WriteRes

%runElab derive "WriteRes" [Show]

export
writeBytes :
     {auto fid : FileDesc a}
  -> a
  -> ByteString
  -> IO (Either FileErr WriteRes)
writeBytes fd (BS n $ BV b o _) =
  fromPrim $ \w =>
    let MkIORes r w := prim__write (fileDesc fd) (unsafeGetBuffer b) (cast o) (cast n) w
     in case r < 0 of
          True => case fromRes r of
            EAGAIN => MkIORes (Right WAgain) w
            x      => MkIORes (Left $ WriteErr x) w
          False => MkIORes (Right $ Written (cast r)) w

export
write : {n : _} -> FileDesc a => a -> IBuffer n -> IO (Either FileErr WriteRes)
write fd ibuf = writeBytes fd (fromIBuffer ibuf)

||| Moves the file pointer to the given offset relative to the
||| `Whence` value.
export %inline
lseek : HasIO io => FileDesc a => a -> OffT -> Whence -> io OffT
lseek fd offset whence =
  primIO $ prim__lseek (fileDesc fd) offset (cast $ whenceCode whence)

export
getFlags : FileDesc a => a -> IO (Either FileErr Flags)
getFlags fd =
  fromPrim $ \w =>
    let MkIORes r w := prim__getFlags (fileDesc fd) w
     in case r < 0 of
          True  => MkIORes (resErr r FlagsErr) w
          False => MkIORes (Right $ F r) w

export
setFlags : FileDesc a => a -> Flags -> IO (Either FileErr ())
setFlags fd (F fs) =
  fromPrim $ \w =>
    let MkIORes r w := prim__setFlags (fileDesc fd) fs w
     in case r < 0 of
          True  => MkIORes (resErr r FlagsErr) w
          False => MkIORes (Right ()) w

export
addFlags : FileDesc a => a -> Flags -> IO (Either FileErr ())
addFlags fd fs = do
  Right x <- getFlags fd | Left err => pure (Left err)
  setFlags fd (x <+> fs)
