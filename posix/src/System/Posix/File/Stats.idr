module System.Posix.File.Stats

import Data.C.Integer
import Data.C.Struct
import Derive.Prelude
import System.Posix.Errno
import System.Posix.File
import System.Posix.File.Type
import System.Posix.Time

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Statvfs
--------------------------------------------------------------------------------

export %foreign "C:calloc_statvfs, posix-idris"
calloc_statvfs: PrimIO AnyPtr

export %foreign "C:get_statvfs_f_bsize, posix-idris"
get_statvfs_f_bsize: AnyPtr -> PrimIO ULong

export %foreign "C:get_statvfs_f_frsize, posix-idris"
get_statvfs_f_frsize: AnyPtr -> PrimIO ULong

export %foreign "C:get_statvfs_f_blocks, posix-idris"
get_statvfs_f_blocks: AnyPtr -> PrimIO FsBlkCntT

export %foreign "C:get_statvfs_f_bfree, posix-idris"
get_statvfs_f_bfree: AnyPtr -> PrimIO FsBlkCntT

export %foreign "C:get_statvfs_f_bavail, posix-idris"
get_statvfs_f_bavail: AnyPtr -> PrimIO FsBlkCntT

export %foreign "C:get_statvfs_f_files, posix-idris"
get_statvfs_f_files: AnyPtr -> PrimIO FsFilCntT

export %foreign "C:get_statvfs_f_ffree, posix-idris"
get_statvfs_f_ffree: AnyPtr -> PrimIO FsFilCntT

export %foreign "C:get_statvfs_f_favail, posix-idris"
get_statvfs_f_favail: AnyPtr -> PrimIO FsFilCntT

export %foreign "C:get_statvfs_f_fsid, posix-idris"
get_statvfs_f_fsid: AnyPtr -> PrimIO ULong

export %foreign "C:get_statvfs_f_flag, posix-idris"
get_statvfs_f_flag: AnyPtr -> PrimIO ULong

export %foreign "C:get_statvfs_f_namemax, posix-idris"
get_statvfs_f_namemax: AnyPtr -> PrimIO ULong

export %foreign "C:set_statvfs_f_bsize, posix-idris"
set_statvfs_f_bsize: AnyPtr -> ULong -> PrimIO ()

public export
record Statvfs where
  constructor SF
  blockSize            : ULong
  fundamentalBlockSize : ULong
  blocks               : FsBlkCntT
  freeBlocks           : FsBlkCntT
  availableBlocks      : FsBlkCntT
  files                : FsFilCntT
  freeFiles            : FsFilCntT
  availableFiles       : FsFilCntT
  fsID                 : ULong
  flags                : ULong
  namemax              : ULong

%runElab derive "Statvfs" [Show,Eq]

export
toStatvfs : AnyPtr -> IO Statvfs
toStatvfs p = do
  x0  <- fromPrim $ get_statvfs_f_bsize p
  x1  <- fromPrim $ get_statvfs_f_frsize p
  x2  <- fromPrim $ get_statvfs_f_blocks p
  x3  <- fromPrim $ get_statvfs_f_bfree p
  x4  <- fromPrim $ get_statvfs_f_bavail p
  x5  <- fromPrim $ get_statvfs_f_files p
  x6  <- fromPrim $ get_statvfs_f_ffree p
  x7  <- fromPrim $ get_statvfs_f_favail p
  x8  <- fromPrim $ get_statvfs_f_fsid p
  x9  <- fromPrim $ get_statvfs_f_flag p
  x10 <- fromPrim $ get_statvfs_f_namemax p
  pure (SF x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)

%inline
withStatvfs : (AnyPtr -> IO a) -> IO a
withStatvfs f = do
  v <- fromPrim $ calloc_statvfs
  res <- f v
  free v
  pure res

--------------------------------------------------------------------------------
-- Stat
--------------------------------------------------------------------------------

export %foreign "C:calloc_stat, posix-idris"
calloc_stat: PrimIO AnyPtr

export %foreign "C:get_stat_st_dev, posix-idris"
get_stat_st_dev: AnyPtr -> PrimIO DevT

export %foreign "C:get_stat_st_ino, posix-idris"
get_stat_st_ino: AnyPtr -> PrimIO InoT

export %foreign "C:get_stat_st_mode, posix-idris"
get_stat_st_mode: AnyPtr -> PrimIO ModeT

export %foreign "C:get_stat_st_nlink, posix-idris"
get_stat_st_nlink: AnyPtr -> PrimIO NlinkT

export %foreign "C:get_stat_st_uid, posix-idris"
get_stat_st_uid: AnyPtr -> PrimIO UidT

export %foreign "C:get_stat_st_gid, posix-idris"
get_stat_st_gid: AnyPtr -> PrimIO GidT

export %foreign "C:get_stat_st_rdev, posix-idris"
get_stat_st_rdev: AnyPtr -> PrimIO DevT

export %foreign "C:get_stat_st_size, posix-idris"
get_stat_st_size: AnyPtr -> PrimIO SizeT

export %foreign "C:get_stat_st_blksize, posix-idris"
get_stat_st_blksize: AnyPtr -> PrimIO BlkSizeT

export %foreign "C:get_stat_st_blocks, posix-idris"
get_stat_st_blocks: AnyPtr -> PrimIO BlkCntT

export %foreign "C:get_stat_st_atim, posix-idris"
get_stat_st_atim: AnyPtr -> PrimIO AnyPtr

export %foreign "C:get_stat_st_mtim, posix-idris"
get_stat_st_mtim: AnyPtr -> PrimIO AnyPtr

export %foreign "C:get_stat_st_ctim, posix-idris"
get_stat_st_ctim: AnyPtr -> PrimIO AnyPtr

%inline
withStat : (AnyPtr -> IO a) -> IO a
withStat f = do
  v <- fromPrim $ calloc_stat
  res <- f v
  free v
  pure res

public export
record FileStats where
  constructor FS
  dev     : DevT
  ino     : InoT
  type    : FileType
  mode    : ModeT
  nlink   : NlinkT
  uid     : UidT
  gid     : GidT
  rdev    : DevT
  size    : SizeT
  blksize : BlkSizeT
  blocks  : BlkCntT
  atime   : Clock UTC
  mtime   : Clock UTC
  ctime   : Clock UTC

%runElab derive "FileStats" [Show,Eq]

export
toFileStats : AnyPtr -> IO FileStats
toFileStats p = do
  x0  <- fromPrim $ get_stat_st_dev p
  x1  <- fromPrim $ get_stat_st_ino p
  x2  <- fromPrim $ get_stat_st_mode p
  x3  <- fromPrim $ get_stat_st_nlink p
  x4  <- fromPrim $ get_stat_st_uid p
  x5  <- fromPrim $ get_stat_st_gid p
  x6  <- fromPrim $ get_stat_st_rdev p
  x7  <- fromPrim $ get_stat_st_size p
  x8  <- fromPrim $ get_stat_st_blksize p
  x9  <- fromPrim $ get_stat_st_blocks p
  x10 <- fromPrim (get_stat_st_atim p) >>= toClock
  x11 <- fromPrim (get_stat_st_mtim p) >>= toClock
  x12 <- fromPrim (get_stat_st_ctim p) >>= toClock
  pure (FS x0 x1 (fromMode x2) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:statvfs, posix-idris"
prim__statvfs : String -> AnyPtr -> PrimIO CInt

%foreign "C:fstatvfs, posix-idris"
prim__fstatvfs : Bits32 -> AnyPtr -> PrimIO CInt

%foreign "C:li_stat, posix-idris"
prim__stat : String -> AnyPtr -> PrimIO CInt

%foreign "C:lstat, posix-idris"
prim__lstat : String -> AnyPtr -> PrimIO CInt

%foreign "C:fstat, posix-idris"
prim__fstat : Bits32 -> AnyPtr -> PrimIO CInt

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

export %inline
statvfs : String -> IO (Either Errno Statvfs)
statvfs s = withStatvfs $ \p => toRes (toStatvfs p) (prim__statvfs s p)

export %inline
fstatvfs : FileDesc a => a -> IO (Either Errno Statvfs)
fstatvfs fd =
  withStatvfs $ \p => toRes (toStatvfs p) (prim__fstatvfs (fileDesc fd) p)

export %inline
stat : String -> IO (Either Errno FileStats)
stat s = withStat $ \p => toRes (toFileStats p) (prim__stat s p)

export %inline
lstat : String -> IO (Either Errno FileStats)
lstat s = withStat $ \p => toRes (toFileStats p) (prim__lstat s p)

export
fstat : FileDesc a => a -> IO (Either Errno FileStats)
fstat fd =
  withStat $ \p => toRes (toFileStats p) (prim__fstat (fileDesc fd) p)
