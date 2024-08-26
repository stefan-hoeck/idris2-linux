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

%default total
%language ElabReflection
%hide Language.Reflection.TTImp.Mode

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:open, linux-idris"
prim__open : String -> CInt -> ModeT -> PrimIO CInt

%foreign "C:close, linux-idris"
prim__close : Bits32 -> PrimIO CInt

%foreign "C__collect_safe:read, linux-idris"
prim__read : (file : Bits32) -> Buffer -> (max : Bits32) -> PrimIO SsizeT

%foreign "C__collect_safe:li_write, linux-idris"
prim__write : (file : Bits32) -> Buffer -> (off,max : Bits32) -> PrimIO SsizeT

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

%runElab derive "FileErr" [Show,Eq]

export
Interpolation FileErr where
  interpolate (OpenErr p x) = "Error when opening \{p}: \{x}"
  interpolate (CloseErr x)  = "Error when closing file descriptor: \{x}"
  interpolate (ReadErr x)   = "Error when reading from file descriptor: \{x}"
  interpolate (WriteErr x)  = "Error when writing to file descriptor: \{x}"

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

||| Tries to open a file with the given flags and mode.
export %inline
openFile : FilePath -> Flags -> Mode -> IO (Either FileErr Bits32)
openFile pth (F f) (M m) =
  fromPrim $ \w => case prim__open (interpolate pth) f m w of
    MkIORes (-1) w => primError (OpenErr pth) w
    MkIORes fd   w => MkIORes (Right $ cast fd) w

||| Closes a file descriptor.
export %inline
close : FileDesc a => a -> IO (Either FileErr ())
close fd =
  fromPrim $ \w => case prim__close (fileDesc fd) w of
    MkIORes (-1) w => primError CloseErr w
    MkIORes _    w => MkIORes (Right ()) w

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
          (-1) => case toPrim lastError w of
            MkIORes EAGAIN w => MkIORes (Right Again) w
            MkIORes x      w => MkIORes (Left $ ReadErr x) w
          0    => MkIORes (Right EOF) w
          x    => MkIORes (Right $ Bytes $ unsafeByteString (cast x) buf) w

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
    let MkIORes wr w := prim__write (fileDesc fd) (unsafeGetBuffer b) (cast o) (cast n) w
     in case wr of
          (-1) => case toPrim lastError w of
            MkIORes EAGAIN w => MkIORes (Right WAgain) w
            MkIORes x      w => MkIORes (Left $ WriteErr x) w
          x => MkIORes (Right $ Written (cast x)) w

export
write : {n : _} -> FileDesc a => a -> IBuffer n -> IO (Either FileErr WriteRes)
write fd ibuf = writeBytes fd (fromIBuffer ibuf)
