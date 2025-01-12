module System.Posix.File.Stats

import Data.C.Ptr
import Derive.Prelude
import System.Clock
import System.Posix.Errno
import System.Posix.File.FileDesc
import System.Posix.File.ReadRes
import System.Posix.File.Type
import System.Posix.Time

%default total
%language ElabReflection

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
record SStatvfs where
  constructor SSF
  ptr : AnyPtr

export %inline
Struct SStatvfs where
  wrap   = SSF
  unwrap = ptr

export %inline
SizeOf SStatvfs where
  sizeof_ = statvfs_size

export
InIO SStatvfs where

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
toStatvfs : SStatvfs -> F1 [World] Statvfs
toStatvfs (SSF p) t =
  let bs  # t := ffi (get_statvfs_f_bsize p) t
      fbs # t := ffi (get_statvfs_f_frsize p) t
      bls # t := ffi (get_statvfs_f_blocks p) t
      frs # t := ffi (get_statvfs_f_bfree p) t
      abs # t := ffi (get_statvfs_f_bavail p) t
      fis # t := ffi (get_statvfs_f_files p) t
      ffs # t := ffi (get_statvfs_f_ffree p) t
      afs # t := ffi (get_statvfs_f_favail p) t
      fid # t := ffi (get_statvfs_f_fsid p) t
      flg # t := ffi (get_statvfs_f_flag p) t
      max # t := ffi (get_statvfs_f_namemax p) t
   in SF bs fbs bls frs abs fis ffs afs fid flg max # t

%inline
withStatvfs : (AnyPtr -> PrimIO CInt) -> EPrim Statvfs
withStatvfs act =
  withStruct SStatvfs $ \s,t =>
    let R _ t := toUnit (act $ unwrap s) t | E x t => E x t
        r # t := toStatvfs s  t
     in R r t

export %inline %hint
convertStatvfs : Convert Statvfs
convertStatvfs = C SStatvfs toStatvfs

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
record SFileStats where
  constructor SFS
  ptr : AnyPtr

export %inline
Struct SFileStats where
  wrap   = SFS
  unwrap = ptr

export %inline
SizeOf SFileStats where
  sizeof_ = stat_size

public export
record FileStats where
  constructor FS
  dev : DevT
  ino : InoT
  mode : ModeT
  nlink : NlinkT
  uid : UidT
  gid : GidT
  rdev : DevT
  size : SizeT
  blksize : BlkSizeT
  blocks : BlkCntT
  atime : Clock UTC
  mtime : Clock UTC
  ctime : Clock UTC

%runElab derive "FileStats" [Show,Eq]

utc : PrimIO AnyPtr -> F1 [World] (Clock UTC)
utc act t =
  let p # t := toF1 act t
   in toClock (wrap p) t

export
fileStats : SFileStats -> F1 [World] FileStats
fileStats (SFS p) t =
  let dev  # t := toF1 (get_stat_st_dev p) t
      ino  # t := toF1 (get_stat_st_ino p) t
      mode # t := toF1 (get_stat_st_mode p) t
      lnk  # t := toF1 (get_stat_st_nlink p) t
      uid  # t := toF1 (get_stat_st_uid p) t
      gid  # t := toF1 (get_stat_st_gid p) t
      rdv  # t := toF1 (get_stat_st_rdev p) t
      siz  # t := toF1 (get_stat_st_size p) t
      bsz  # t := toF1 (get_stat_st_blksize p) t
      bls  # t := toF1 (get_stat_st_blocks p) t
      ati  # t := utc (get_stat_st_atim p) t
      mti  # t := utc (get_stat_st_mtim p) t
      cti  # t := utc (get_stat_st_ctim p) t
   in FS dev ino mode lnk uid gid rdv siz bsz bls ati mti cti # t

%inline
withFileStats : (AnyPtr -> PrimIO CInt) -> EPrim FileStats
withFileStats act =
  withStruct SFileStats $ \s,t =>
    let R _ t := toUnit (act $ unwrap s) t | E x t => E x t
        r # t := fileStats s t
     in R r t

export %inline %hint
convertFileStats : Convert FileStats
convertFileStats = C SFileStats fileStats

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
statvfs : String -> EPrim Statvfs
statvfs s = withStatvfs (prim__statvfs s)

export %inline
fstatvfs : FileDesc a => a -> EPrim Statvfs
fstatvfs fd = withStatvfs (prim__fstatvfs (fileDesc fd))

export %inline
stat : String -> EPrim FileStats
stat s = withFileStats (prim__stat s)

export %inline
lstat : String -> EPrim FileStats
lstat s = withFileStats (prim__lstat s)

export
fstat : FileDesc a => a -> EPrim FileStats
fstat fd = withFileStats (prim__fstat (fileDesc fd))
