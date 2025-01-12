module System.Linux.Inotify.Inotify

import Data.C.Ptr
import Derive.Prelude
import System.Posix.File.FileDesc
import System.Posix.File.ReadRes
import System.Linux.Inotify.Flags

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:li_inotify_more, linux-idris"
prim__inotify_more : AnyPtr -> AnyPtr -> Bits32 -> Bits32

%foreign "C:li_inotify_next, linux-idris"
prim__inotify_next : AnyPtr -> AnyPtr

%foreign "C:li_inotify_wd, linux-idris"
prim__inotify_wd : AnyPtr -> Bits32

%foreign "C:li_inotify_mask, linux-idris"
prim__inotify_mask : AnyPtr -> Bits32

%foreign "C:li_inotify_cookie, linux-idris"
prim__inotify_cookie : AnyPtr -> Bits32

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

||| An `inotify` file descriptor.
export
record Inotify where
  constructor I
  fd : Bits32

export %inline
Cast Inotify Fd where cast = cast . fd

export %inline
Cast CInt Inotify where cast = I . cast

%runElab derive "Inotify" [Show,Eq,Ord]

||| An `inotify` file descriptor.
export
record Watch where
  constructor W
  wd : Bits32

%runElab derive "Watch" [Show,Eq,Ord]

export %inline
Interpolation Watch where interpolate = show . wd

export %inline
Cast CInt Watch where cast = W . cast

export %inline
Cast Watch Bits32 where cast = wd

public export
record InotifyRes where
  constructor IR
  watch  : Watch
  mask   : InotifyMask
  cookie : Bits32
  name   : String

%runElab derive "InotifyRes" [Show,Eq]


reslt : AnyPtr -> InotifyRes
reslt p =
  IR
    { watch  = W $ prim__inotify_wd p
    , mask   = IM $ prim__inotify_mask p
    , cookie = prim__inotify_cookie p
    , name   = ""
    }

export
results : SnocList InotifyRes -> AnyPtr -> AnyPtr -> Bits32 -> List InotifyRes
results sx orig cur sz =
  case prim__inotify_more orig cur sz of
    0 => sx <>> []
    _ =>
      results
        (sx :< reslt cur)
        orig
        (assert_smaller cur $ prim__inotify_next cur)
        sz

export
FromPtr (List InotifyRes) where
  fromPtr (CP sz p) t = results [<] p p sz # t

export %inline
FromBuf (List InotifyRes) where
  fromBuf = viaPtrFromBuf
