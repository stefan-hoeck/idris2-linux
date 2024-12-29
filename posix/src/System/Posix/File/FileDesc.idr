module System.Posix.File.FileDesc

import Data.C.Ptr
import Derive.Prelude

%default total
%language ElabReflection

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
