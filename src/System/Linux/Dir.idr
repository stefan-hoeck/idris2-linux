module System.Linux.Dir

import Data.Buffer
import public Data.Buffer.Core
import public Data.ByteString
import public Data.C.Integer
import public Data.FilePath
import public System.Linux.Error
import public System.Linux.File

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_mkdir, linux-idris"
prim__mkdir : String -> ModeT -> PrimIO CInt

%foreign "C:li_rmdir, linux-idris"
prim__rmdir : String -> PrimIO CInt

%foreign "C:calloc_dir, linux-idris"
prim__calloc_dir : PrimIO AnyPtr

%foreign "C:li_opendir, linux-idris"
prim__opendir : String -> AnyPtr -> PrimIO CInt

%foreign "C:li_fdopendir, linux-idris"
prim__fdopendir : Bits32 -> AnyPtr -> PrimIO CInt

%foreign "C:li_closedir, linux-idris"
prim__closedir : AnyPtr -> PrimIO CInt

%foreign "C:li_rewinddir, linux-idris"
prim__rewinddir : AnyPtr -> PrimIO ()

%foreign "C:li_readdir, linux-idris"
prim__readdir : AnyPtr -> Buffer -> PrimIO SsizeT

%foreign "C:li_getcwd, linux-idris"
prim__getcwd : Buffer -> (max : Bits32) -> PrimIO SsizeT

%foreign "C:li_chdir, linux-idris"
prim__chdir : String -> PrimIO CInt

%foreign "C:li_chroot, linux-idris"
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
mkdir : (pth : FilePath) -> Mode -> IO (Either FileErr ())
mkdir f (M m) = toUnit FilErr $ prim__mkdir "\{f}" m

||| Creates a new directory including all its parent directories
|||
||| Note: This does not fail with an error if the directory in question
|||       already exists.
export
mkpdir : (pth : FilePath) -> Mode -> IO (Either FileErr ())
mkpdir (FP p) (M m) =
  go (p :: parentDirs p) >>= \case
    Right ()    => pure (Right ())
    Left EEXIST => pure (Right ())
    Left x      => pure (Left $ FilErr x)

  where
    go : List (Path t) -> IO (Either Error ())
    go []     = pure $ Right ()
    go (h::t) =
      go t >>= \case
        Right ()    => toUnit id $ prim__mkdir "\{FP h}" m
        Left EEXIST => toUnit id $ prim__mkdir "\{FP h}" m
        Left EACCES => toUnit id $ prim__mkdir "\{FP h}" m
        Left x      => pure (Left x)

||| Opens a directory.
export
opendir : FilePath -> IO (Either FileErr Dir)
opendir s = do
  p <- fromPrim $ prim__calloc_dir
  toRes OpenDir (pure $ MkDir p) $ prim__opendir "\{s}" p

||| Opens a directory from a file descriptor.
export
fdopendir : FileDesc a => a -> IO (Either FileErr Dir)
fdopendir fd = do
  p <- fromPrim $ prim__calloc_dir
  toRes OpenDir (pure $ MkDir p) $ prim__fdopendir (fileDesc fd) p

||| Closes a directory.
export
rewinddir : Dir -> IO ()
rewinddir (MkDir p) = fromPrim $ prim__rewinddir p

||| Closes a directory.
export
closedir : Dir -> IO (Either FileErr ())
closedir (MkDir p) = toUnit CloseDir $ prim__closedir p

||| Reads the next entry from a directory.
export
readdir : Dir -> IO (Either FileErr $ Maybe ByteString)
readdir (MkDir p) = do
  toBytesMaybe $ \w =>
    let MkIORes buf w := prim__newBuf 256 w
        MkIORes rd  w := prim__readdir p buf w
     in MkIORes (buf,rd) w

||| Returns the current working directory.
export
getcwd : IO (Either FileErr ByteString)
getcwd =
  toBytes $ \w =>
    let MkIORes buf w := prim__newBuf 4096 w
        MkIORes rd  w := prim__getcwd buf 4096 w
     in MkIORes (buf,rd) w

||| Changes the current working directory
export
chdir : FilePath -> IO (Either FileErr ())
chdir p = toUnit FilErr $ prim__chdir "\{p}"

||| Changes the current working directory
export
chroot : FilePath -> IO (Either FileErr ())
chroot p = toUnit FilErr $ prim__chroot "\{p}"
