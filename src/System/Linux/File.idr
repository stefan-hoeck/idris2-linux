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

-- TODO: Export this in idris2-array
%foreign "scheme:blodwen-new-buffer"
         "RefC:newBuffer"
         "node:lambda:s=>Buffer.alloc(s)"
prim__newBuffer : Bits32 -> PrimIO Buffer

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
data FileError : Type where
  OpenErr  : FilePath -> Error -> FileError
  CloseErr : Error -> FileError
  ReadErr  : Error -> FileError
  WriteErr : Error -> FileError

%runElab derive "FileError" [Show,Eq]

export
Interpolation FileError where
  interpolate (OpenErr p x) = "Error when opening \{p}: \{x}"
  interpolate (CloseErr x)  = "Error when closing file descriptor: \{x}"
  interpolate (ReadErr x)   = "Error when reading from file descriptor: \{x}"
  interpolate (WriteErr x)  = "Error when writing to file descriptor: \{x}"

--------------------------------------------------------------------------------
-- Flags
--------------------------------------------------------------------------------

public export
record Flags where
  constructor F
  flags : CInt

%runElab derive "Flags" [Show,Eq,Ord]

public export
Semigroup Flags where
  F x <+> F y = F $ x .|. y

public export
Monoid Flags where neutral = F 0

--------------------------------------------------------------------------------
-- Mode
--------------------------------------------------------------------------------

public export
record Mode where
  constructor M
  mode : ModeT

%runElab derive "Mode" [Show,Eq,Ord]

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
openFile : FilePath -> Flags -> Mode -> IO (Either FileError Bits32)
openFile pth (F f) (M m) =
  fromPrim $ \w => case prim__open (interpolate pth) f m w of
    MkIORes (-1) w => primError (OpenErr pth) w
    MkIORes fd   w => MkIORes (Right $ cast fd) w

||| Closes a file descriptor.
export %inline
close : FileDesc a => a -> IO (Either FileError ())
close fd =
  fromPrim $ \w => case prim__close (fileDesc fd) w of
    MkIORes (-1) w => primError CloseErr w
    MkIORes _    w => MkIORes (Right ()) w

public export
data ReadResult : Type where
  EOF   : ReadResult
  Again : ReadResult
  Err   : Error -> ReadResult
  Bytes : (n : Nat) -> IBuffer n -> ReadResult

%runElab derive "ReadResult" [Show]

export
read : FileDesc a => a -> (n : Bits32) -> IO ReadResult
read fd n =
  fromPrim $ \w =>
    let MkIORes buf w := prim__newBuffer n w
        MkIORes rd  w := prim__read (fileDesc fd) buf n w
     in case rd of
          (-1) => case toPrim lastError w of
            MkIORes EAGAIN w => MkIORes Again w
            MkIORes x      w => MkIORes (Err x) w
          0    => MkIORes EOF w
          x    => MkIORes (Bytes (cast x) (unsafeMakeBuffer buf)) w

public export
data WriteResult : Type where
  WAgain  : WriteResult
  WErr    : Error -> WriteResult
  Written : (n : Nat) -> WriteResult

%runElab derive "WriteResult" [Show]

export
writeVect : {n : _} -> FileDesc a => a -> ByteVect n -> IO WriteResult
writeVect fd (BV b o _) =
  fromPrim $ \w =>
    let MkIORes wr w := prim__write (fileDesc fd) (unsafeGetBuffer b) (cast o) (cast n) w
     in case wr of
          (-1) => case toPrim lastError w of
            MkIORes EAGAIN w => MkIORes WAgain w
            MkIORes x      w => MkIORes (WErr x) w
          x => MkIORes (Written (cast x)) w

export
write : {n : _} -> FileDesc a => a -> IBuffer n -> IO WriteResult
write fd ibuf = writeVect fd (BV ibuf 0 reflexive)
