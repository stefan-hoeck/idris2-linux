module System.Posix.Dir

import Data.Buffer
import public Data.Buffer.Core
import public Data.ByteString
import public Data.C.Integer
import public System.Posix.Errno
import public System.Posix.File

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_mkdir, posix-idris"
prim__mkdir : String -> ModeT -> PrimIO CInt

%foreign "C:li_rmdir, posix-idris"
prim__rmdir : String -> PrimIO CInt

%foreign "C:calloc_dir, posix-idris"
prim__calloc_dir : PrimIO AnyPtr

%foreign "C:li_opendir, posix-idris"
prim__opendir : String -> AnyPtr -> PrimIO CInt

%foreign "C:li_fdopendir, posix-idris"
prim__fdopendir : Bits32 -> AnyPtr -> PrimIO CInt

%foreign "C:li_closedir, posix-idris"
prim__closedir : AnyPtr -> PrimIO CInt

%foreign "C:li_rewinddir, posix-idris"
prim__rewinddir : AnyPtr -> PrimIO ()

%foreign "C:li_readdir, posix-idris"
prim__readdir : AnyPtr -> Buffer -> PrimIO SsizeT

%foreign "C:li_getcwd, posix-idris"
prim__getcwd : Buffer -> (max : Bits32) -> PrimIO SsizeT

%foreign "C:li_chdir, posix-idris"
prim__chdir : String -> PrimIO CInt

%foreign "C:li_chroot, posix-idris"
prim__chroot : String -> PrimIO CInt

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

export
record Dir where
  constructor MkDir
  ptr : AnyPtr

||| Creates a new directory.
|||
||| This fails if the directory exists already. It also fails, if the
||| parent directory does not exist.
export %inline
mkdir : (pth : String) -> Mode -> PrimIO (Either Errno ())
mkdir f (M m) = toUnit $ prim__mkdir f m

||| Opens a directory.
export
opendir : String -> PrimIO (Either Errno Dir)
opendir s w =
  let MkIORes p w := prim__calloc_dir w
   in toRes (MkIORes $ MkDir p) (prim__opendir s p) w

||| Opens a directory from a file descriptor.
export
fdopendir : FileDesc a => a -> PrimIO (Either Errno Dir)
fdopendir fd w =
  let MkIORes p w := prim__calloc_dir w
   in toRes (MkIORes $ MkDir p) (prim__fdopendir (fileDesc fd) p) w

||| Closes a directory.
export
rewinddir : Dir -> PrimIO ()
rewinddir (MkDir p) = prim__rewinddir p

||| Closes a directory.
export
closedir : Dir -> PrimIO (Either Errno ())
closedir (MkDir p) = toUnit $ prim__closedir p

||| Reads the next entry from a directory.
export
readdir : Dir -> PrimIO (Either Errno (Maybe ByteString))
readdir (MkDir p) w =
  let MkIORes bs w := toBytes 256 (\b,_ => prim__readdir p b) w
   in case bs of
        Right (BS 0 _) => MkIORes (Right Nothing) w
        Right bs       => MkIORes (Right $ Just bs) w
        Left x         => MkIORes (Left x) w

||| Returns the current working directory.
export %inline
getcwd : PrimIO (Either Errno ByteString)
getcwd = toBytes 4096 (prim__getcwd)

||| Changes the current working directory
export
chdir : String -> PrimIO (Either Errno ())
chdir p = toUnit $ prim__chdir p

||| Changes the current working directory
export
chroot : String -> PrimIO (Either Errno ())
chroot p = toUnit $ prim__chroot p
