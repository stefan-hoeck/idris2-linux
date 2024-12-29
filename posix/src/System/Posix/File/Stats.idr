module System.Posix.File.Stats

import Data.C.Ptr
import Derive.Prelude
import System.Clock
import System.Posix.Errno
import System.Posix.File.FileDesc
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
toStatvfs : SStatvfs -> PrimIO Statvfs
toStatvfs (SSF p) w =
  let MkIORes bs  w :=  get_statvfs_f_bsize p w
      MkIORes fbs w :=  get_statvfs_f_frsize p w
      MkIORes bls w :=  get_statvfs_f_blocks p w
      MkIORes frs w :=  get_statvfs_f_bfree p w
      MkIORes abs w :=  get_statvfs_f_bavail p w
      MkIORes fis w :=  get_statvfs_f_files p w
      MkIORes ffs w :=  get_statvfs_f_ffree p w
      MkIORes afs w :=  get_statvfs_f_favail p w
      MkIORes fid w :=  get_statvfs_f_fsid p w
      MkIORes flg w :=  get_statvfs_f_flag p w
      MkIORes max w :=  get_statvfs_f_namemax p w
   in MkIORes (SF bs fbs bls frs abs fis ffs afs fid flg max) w

%inline
withStatvfs : (AnyPtr -> PrimIO CInt) -> EPrim Statvfs
withStatvfs act =
  withStruct SStatvfs $ \s,w =>
    let R _ w       := toUnit (act $ unwrap s) w | E x w => E x w
        MkIORes r w := toStatvfs s  w
     in R r w

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

utc : PrimIO AnyPtr -> PrimIO (Clock UTC)
utc act w =
  let MkIORes p w := act w
   in toClock (wrap p) w

export
fileStats : SFileStats -> PrimIO FileStats
fileStats (SFS p) w =
  let MkIORes dev  w :=  get_stat_st_dev p w
      MkIORes ino  w :=  get_stat_st_ino p w
      MkIORes mode w :=  get_stat_st_mode p w
      MkIORes lnk  w :=  get_stat_st_nlink p w
      MkIORes uid  w :=  get_stat_st_uid p w
      MkIORes gid  w :=  get_stat_st_gid p w
      MkIORes rdv  w :=  get_stat_st_rdev p w
      MkIORes siz  w :=  get_stat_st_size p w
      MkIORes bsz  w :=  get_stat_st_blksize p w
      MkIORes bls  w :=  get_stat_st_blocks p w
      MkIORes ati  w :=  utc (get_stat_st_atim p) w
      MkIORes mti  w :=  utc (get_stat_st_mtim p) w
      MkIORes cti  w :=  utc (get_stat_st_ctim p) w
   in MkIORes (FS dev ino mode lnk uid gid rdv siz bsz bls ati mti cti) w

%inline
withFileStats : (AnyPtr -> PrimIO CInt) -> EPrim FileStats
withFileStats act =
  withStruct SFileStats $ \s,w =>
    let R _ w       := toUnit (act $ unwrap s) w | E x w => E x w
        MkIORes r w := fileStats s w
     in R r w

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
