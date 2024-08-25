module System.Linux.File

import Data.Bits
import Data.C.Integer
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

%runElab derive "FileError" [Show,Eq]

export
Interpolation FileError where
  interpolate (OpenErr p x) = "Error when opening \{p}: \{x}"
  interpolate (CloseErr x)  = "Error when closing file descriptor: \{x}"

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
