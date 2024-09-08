module System.Posix.File.Stats

import Data.C.Ptr
import Derive.Prelude
import System.Posix.Errno
import System.Posix.File
import System.Posix.File.Type
import System.Posix.Time

%default total

--------------------------------------------------------------------------------
-- StatvFS
--------------------------------------------------------------------------------

%foreign "C:get_statvfs_f_bsize, linux-idris"
get_statvfs_f_bsize: AnyPtr -> PrimIO ULong

%foreign "C:get_statvfs_f_frsize, linux-idris"
get_statvfs_f_frsize: AnyPtr -> PrimIO ULong

%foreign "C:get_statvfs_f_blocks, linux-idris"
get_statvfs_f_blocks: AnyPtr -> PrimIO FsBlkCntT

%foreign "C:get_statvfs_f_bfree, linux-idris"
get_statvfs_f_bfree: AnyPtr -> PrimIO FsBlkCntT

%foreign "C:get_statvfs_f_bavail, linux-idris"
get_statvfs_f_bavail: AnyPtr -> PrimIO FsBlkCntT

%foreign "C:get_statvfs_f_files, linux-idris"
get_statvfs_f_files: AnyPtr -> PrimIO FsFilCntT

%foreign "C:get_statvfs_f_ffree, linux-idris"
get_statvfs_f_ffree: AnyPtr -> PrimIO FsFilCntT

%foreign "C:get_statvfs_f_favail, linux-idris"
get_statvfs_f_favail: AnyPtr -> PrimIO FsFilCntT

%foreign "C:get_statvfs_f_fsid, linux-idris"
get_statvfs_f_fsid: AnyPtr -> PrimIO ULong

%foreign "C:get_statvfs_f_flag, linux-idris"
get_statvfs_f_flag: AnyPtr -> PrimIO ULong

%foreign "C:get_statvfs_f_namemax, linux-idris"
get_statvfs_f_namemax: AnyPtr -> PrimIO ULong

export
record Statvfs where
  constructor SF
  ptr : AnyPtr

export %inline
Struct Statvfs where
  wrap   = SF
  unwrap = ptr

export %inline
SizeOf Statvfs where
  sizeof_ = statvfs_size

namespace Statvfs
  export %inline
  blockSize : HasIO io => Statvfs -> io ULong
  blockSize s = primIO $ get_statvfs_f_bsize s.ptr

  export %inline
  fundamentalBlockSize : HasIO io => Statvfs -> io ULong
  fundamentalBlockSize s = primIO $ get_statvfs_f_frsize s.ptr

  export %inline
  blocks : HasIO io => Statvfs -> io FsBlkCntT
  blocks s = primIO $ get_statvfs_f_blocks s.ptr

  export %inline
  freeBlocks : HasIO io => Statvfs -> io FsBlkCntT
  freeBlocks s = primIO $ get_statvfs_f_bfree s.ptr

  export %inline
  availableBlocks : HasIO io => Statvfs -> io FsBlkCntT
  availableBlocks s = primIO $ get_statvfs_f_bavail s.ptr

  export %inline
  files : HasIO io => Statvfs -> io FsFilCntT
  files s = primIO $ get_statvfs_f_files s.ptr

  export %inline
  freeFiles : HasIO io => Statvfs -> io FsFilCntT
  freeFiles s = primIO $ get_statvfs_f_ffree s.ptr

  export %inline
  availableFiles : HasIO io => Statvfs -> io FsFilCntT
  availableFiles s = primIO $ get_statvfs_f_favail s.ptr

  export %inline
  fsID : HasIO io => Statvfs -> io ULong
  fsID s = primIO $ get_statvfs_f_fsid s.ptr

  export %inline
  flags : HasIO io => Statvfs -> io ULong
  flags s = primIO $ get_statvfs_f_flag s.ptr

  export %inline
  namemax : HasIO io => Statvfs -> io ULong
  namemax s = primIO $ get_statvfs_f_namemax s.ptr

--------------------------------------------------------------------------------
-- FileStats
--------------------------------------------------------------------------------

%foreign "C:get_stat_st_dev, linux-idris"
get_stat_st_dev: AnyPtr -> PrimIO DevT

%foreign "C:get_stat_st_ino, linux-idris"
get_stat_st_ino: AnyPtr -> PrimIO InoT

%foreign "C:get_stat_st_mode, linux-idris"
get_stat_st_mode: AnyPtr -> PrimIO ModeT

%foreign "C:get_stat_st_nlink, linux-idris"
get_stat_st_nlink: AnyPtr -> PrimIO NlinkT

%foreign "C:get_stat_st_uid, linux-idris"
get_stat_st_uid: AnyPtr -> PrimIO UidT

%foreign "C:get_stat_st_gid, linux-idris"
get_stat_st_gid: AnyPtr -> PrimIO GidT

%foreign "C:get_stat_st_rdev, linux-idris"
get_stat_st_rdev: AnyPtr -> PrimIO DevT

%foreign "C:get_stat_st_size, linux-idris"
get_stat_st_size: AnyPtr -> PrimIO SizeT

%foreign "C:get_stat_st_blksize, linux-idris"
get_stat_st_blksize: AnyPtr -> PrimIO BlkSizeT

%foreign "C:get_stat_st_blocks, linux-idris"
get_stat_st_blocks: AnyPtr -> PrimIO BlkCntT

%foreign "C:get_stat_st_atim, linux-idris"
get_stat_st_atim: AnyPtr -> PrimIO AnyPtr

%foreign "C:get_stat_st_mtim, linux-idris"
get_stat_st_mtim: AnyPtr -> PrimIO AnyPtr

%foreign "C:get_stat_st_ctim, linux-idris"
get_stat_st_ctim: AnyPtr -> PrimIO AnyPtr

export
record FileStats where
  constructor FS
  ptr : AnyPtr

export %inline
Struct FileStats where
  wrap   = FS
  unwrap = ptr

export %inline
SizeOf FileStats where
  sizeof_ = stat_size

namespace FileStats
  export %inline
  dev : HasIO io => FileStats -> io DevT
  dev s = primIO $ get_stat_st_dev s.ptr

  export %inline
  ino : HasIO io => FileStats -> io InoT
  ino s = primIO $ get_stat_st_ino s.ptr

  export %inline
  mode : HasIO io => FileStats -> io ModeT
  mode s = primIO $ get_stat_st_mode s.ptr

  export %inline
  nlink : HasIO io => FileStats -> io NlinkT
  nlink s = primIO $ get_stat_st_nlink s.ptr

  export %inline
  uid : HasIO io => FileStats -> io UidT
  uid s = primIO $ get_stat_st_uid s.ptr

  export %inline
  gid : HasIO io => FileStats -> io GidT
  gid s = primIO $ get_stat_st_gid s.ptr

  export %inline
  rdev : HasIO io => FileStats -> io DevT
  rdev s = primIO $ get_stat_st_rdev s.ptr

  export %inline
  size : HasIO io => FileStats -> io SizeT
  size s = primIO $ get_stat_st_size s.ptr

  export %inline
  blksize : HasIO io => FileStats -> io BlkSizeT
  blksize s = primIO $ get_stat_st_blksize s.ptr

  export %inline
  blocks : HasIO io => FileStats -> io BlkCntT
  blocks s = primIO $ get_stat_st_blocks s.ptr

  export %inline
  atime : HasIO io => FileStats -> io AnyPtr
  atime s = primIO $ get_stat_st_atim s.ptr

  export %inline
  mtime : HasIO io => FileStats -> io AnyPtr
  mtime s = primIO $ get_stat_st_mtim s.ptr

  export %inline
  ctime : HasIO io => FileStats -> io AnyPtr
  ctime s = primIO $ get_stat_st_ctim s.ptr

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
statvfs : String -> Statvfs -> IO (Either Errno ())
statvfs s p = toUnit $ prim__statvfs s p.ptr

export %inline
fstatvfs : FileDesc a => a -> Statvfs -> IO (Either Errno ())
fstatvfs fd p = toUnit $ prim__fstatvfs (fileDesc fd) p.ptr

export %inline
stat : String -> FileStats -> IO (Either Errno ())
stat s p = toUnit $ prim__stat s p.ptr

export %inline
lstat : String -> FileStats -> IO (Either Errno ())
lstat s p = toUnit $ prim__lstat s p.ptr

export
fstat : FileDesc a => a -> FileStats -> IO (Either Errno ())
fstat fd p = toUnit $ prim__fstat (fileDesc fd) p.ptr
