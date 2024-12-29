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
opendir s w =
  let MkIORes p w := prim__calloc_dir w
   in toVal (const $ wrapdir p) (prim__opendir s p) w

||| Opens a directory from a file descriptor.
export
fdopendir : FileDesc a => a -> EPrim Dir
fdopendir fd w =
  let MkIORes p w := prim__calloc_dir w
   in toRes (MkIORes $ wrapdir p) (prim__fdopendir (fileDesc fd) p) w

||| Rewinds a directory.
export
rewinddir : Dir -> PrimIO ()
rewinddir p = prim__rewinddir (dirptr p)

||| Closes a directory.
export
closedir : Dir -> EPrim ()
closedir p = toUnit $ prim__closedir (dirptr p)

||| Reads the next entry from a directory.
export
readdir : Dir -> EPrim (Maybe ByteString)
readdir p w =
  let dp     := dirptr p
      R bs w := toBytes 256 (\b,_ => prim__readdir dp b) w | E x w => E x w
   in case bs of
        BS 0 _ => R Nothing w
        bs     => R (Just bs) w

||| Returns the current working directory.
export %inline
getcwd : EPrim ByteString
getcwd = toBytes 4096 (prim__getcwd)

||| Changes the current working directory
export
chdir : String -> EPrim ()
chdir p = toUnit $ prim__chdir p

||| Changes the current working directory
export
chroot : String -> EPrim ()
chroot p = toUnit $ prim__chroot p
