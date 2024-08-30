module System.Linux.File.Stats

import Data.C.Integer
import Data.C.Struct
import Derive.Prelude
import System.Linux.Error
import System.Linux.File
import System.Linux.Time

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Structs
--------------------------------------------------------------------------------

public export
0 StatvFs : Type
StatvFs =
  Struct "statvfs"
    [ ("f_bsize", ULong)
    , ("f_frsize", ULong)
    , ("f_blocks", FsBlkCntT)
    , ("f_bfree", FsBlkCntT)
    , ("f_bavail", FsBlkCntT)
    , ("f_files", FsFilCntT)
    , ("f_ffree", FsFilCntT)
    , ("f_favail", FsFilCntT)
    , ("f_fsid", ULong)
    , ("f_flag", ULong)
    , ("f_namemax", ULong)
    ]

public export
record FSStats where
  constructor FSS
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

%runElab derive "FSStats" [Show,Eq]

export
toFSStats : StatvFs -> FSStats
toFSStats s =
  FSS
    { blockSize            = getField s "f_bsize"
    , fundamentalBlockSize = getField s "f_frsize"
    , blocks               = getField s "f_blocks"
    , freeBlocks           = getField s "f_bfree"
    , availableBlocks      = getField s "f_bavail"
    , files                = getField s "f_files"
    , freeFiles            = getField s "f_ffree"
    , availableFiles       = getField s "f_favail"
    , fsID                 = getField s "f_fsid"
    , flags                = getField s "f_flag"
    , namemax              = getField s "f_namemax"
    }

public export
0 Stat : Type
Stat =
  Struct "stat"
    [ ("st_dev", DevT)
    , ("st_ino", InoT)
    , ("st_mode", ModeT)
    , ("st_nlink", NlinkT)
    , ("st_uid", UidT)
    , ("st_gid", GidT)
    , ("st_rdev", DevT)
    , ("st_size", OffT)
    , ("st_blksize", BlkSizeT)
    , ("st_blkcnt", BlkCntT)
    ]

public export
record FileStats where
  constructor FS
  dev     : DevT
  ino     : InoT
  mode    : ModeT
  nlink   : NlinkT
  uid     : UidT
  gid     : GidT
  rdev    : DevT
  size    : OffT
  blksize : BlkSizeT
  blkcnt  : BlkCntT
  atime   : Time
  mtime   : Time
  ctime   : Time

%runElab derive "FileStats" [Show,Eq]

export %foreign "C:li_atime, linux-idris"
atime : Stat -> Timespec

export %foreign "C:li_ctime, linux-idris"
ctime : Stat -> Timespec

export %foreign "C:li_mtime, linux-idris"
mtime : Stat -> Timespec

export
toFileStats : Stat -> FileStats
toFileStats s =
  FS
    { dev     = getField s "st_dev"
    , ino     = getField s "st_ino"
    , mode    = getField s "st_mode"
    , nlink   = getField s "st_nlink"
    , uid     = getField s "st_uid"
    , gid     = getField s "st_gid"
    , rdev    = getField s "st_rdev"
    , size    = getField s "st_size"
    , blksize = getField s "st_blksize"
    , blkcnt  = getField s "st_blkcnt"
    , atime   = toTime $ atime s
    , mtime   = toTime $ mtime s
    , ctime   = toTime $ ctime s
    }

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

export %foreign "C:li_allocStatvfs, linux-idris"
prim__allocStatvfs : PrimIO StatvFs

export %foreign "C:li_freeStatvfs, linux-idris"
prim__freeStatvfs : StatvFs -> PrimIO ()

%foreign "C:statvfs, linux-idris"
prim__statvfs : String -> StatvFs -> PrimIO CInt

%foreign "C:fstatvfs, linux-idris"
prim__fstatvfs : Bits32 -> StatvFs -> PrimIO CInt

export %foreign "C:li_allocStat, linux-idris"
prim__allocStat : PrimIO Stat

export %foreign "C:li_freeStat, linux-idris"
prim__freeStat : Stat -> PrimIO ()

%foreign "C:stat, linux-idris"
prim__stat : String -> Stat -> PrimIO CInt

%foreign "C:lstat, linux-idris"
prim__lstat : String -> Stat -> PrimIO CInt

%foreign "C:fstat, linux-idris"
prim__fstat : Bits32 -> Stat -> PrimIO CInt

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

export
statvfs : String -> IO (Either Error FSStats)
statvfs pth = do
  s <- fromPrim $ prim__allocStatvfs
  r <- toRes id (toFSStats s) $ prim__statvfs pth s
  fromPrim $ prim__freeStatvfs s
  pure r

export
fstatvfs : FileDesc a => a -> IO (Either Error FSStats)
fstatvfs fd = do
  s <- fromPrim $ prim__allocStatvfs
  r <- toRes id (toFSStats s) $ prim__fstatvfs (fileDesc fd) s
  fromPrim $ prim__freeStatvfs s
  pure r

export
stat : String -> IO (Either Error FileStats)
stat pth = do
  s <- fromPrim $ prim__allocStat
  r <- toRes id (toFileStats s) $ prim__stat pth s
  fromPrim $ prim__freeStat s
  pure r

export
lstat : String -> IO (Either Error FileStats)
lstat pth = do
  s <- fromPrim $ prim__allocStat
  r <- toRes id (toFileStats s) $ prim__lstat pth s
  fromPrim $ prim__freeStat s
  pure r

export
fstat : FileDesc a => a -> IO (Either Error FileStats)
fstat fd = do
  s <- fromPrim $ prim__allocStat
  r <- toRes id (toFileStats s) $ prim__fstat (fileDesc fd) s
  fromPrim $ prim__freeStat s
  pure r
