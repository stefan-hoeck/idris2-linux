module System.Posix.Dir.Prim

import Data.Buffer
import public Data.Buffer.Core
import public Data.ByteString
import public Data.C.Integer
import public System.Posix.Dir.Dir
import public System.Posix.Errno
import public System.Posix.File.Prim

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

||| Creates a new directory.
|||
||| This fails if the directory exists already. It also fails, if the
||| parent directory does not exist.
export %inline
mkdir : (pth : String) -> Mode -> EPrim ()
mkdir f (M m) = toUnit $ prim__mkdir f m

||| Opens a directory.
export
opendir : String -> EPrim Dir
opendir s t =
  let p # t := ffi prim__calloc_dir t
   in toVal (const $ wrapdir p) (prim__opendir s p) t

||| Opens a directory from a file descriptor.
export
fdopendir : FileDesc a => a -> EPrim Dir
fdopendir fd t =
  let p # t := ffi prim__calloc_dir t
   in toRes (MkIORes $ wrapdir p) (prim__fdopendir (fileDesc fd) p) t

||| Rewinds a directory.
export
rewinddir : Dir -> PrimIO ()
rewinddir p = prim__rewinddir (dirptr p)

||| Closes a directory.
export
closedir : Dir -> EPrim ()
closedir p = toUnit $ prim__closedir (dirptr p)

||| Closes a directory.
export %inline
closedir' : Dir -> F1' World
closedir' p = e1ToF1 (closedir {es = [Errno]} p)

||| Reads the next entry from a directory.
export
readdir : (0 r : Type) -> FromBuf r => Dir -> EPrim (ReadRes r)
readdir r p = toRes 256 (\b,_ => prim__readdir (dirptr p) b)

||| Returns the current working directory.
export %inline
getcwd : (0 r : Type) -> FromBuf r => EPrim r
getcwd r = allocRead 4096 prim__getcwd

||| Changes the current working directory
export
chdir : String -> EPrim ()
chdir p = toUnit $ prim__chdir p

||| Changes the current working directory
export
chroot : String -> EPrim ()
chroot p = toUnit $ prim__chroot p
