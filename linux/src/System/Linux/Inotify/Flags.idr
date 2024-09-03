-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Linux.Inotify.Flags

import Data.Bits
import Derive.Prelude

%default total
%language ElabReflection

public export
record InotifyFlags where
  constructor IF
  flags : Bits32

%runElab derive "InotifyFlags" [Show,Eq,Ord,FromInteger]

public export
Semigroup InotifyFlags where
  IF x <+> IF y = IF $ x .|. y

public export
Monoid InotifyFlags where neutral = IF 0

public export
record InotifyMask where
  constructor IM
  mask : Bits32

namespace InotifyMask
  %runElab derive "InotifyMask" [Show,Eq,Ord,FromInteger]

public export
Semigroup InotifyMask where
  IM x <+> IM y = IM $ x .|. y

public export
Monoid InotifyMask where neutral = IM 0


public export
IN_NONBLOCK : InotifyFlags
IN_NONBLOCK = 2048

public export
IN_CLOEXEC : InotifyFlags
IN_CLOEXEC = 524288

public export
IN_ACCESS : InotifyMask
IN_ACCESS = 1

public export
IN_ATTRIB : InotifyMask
IN_ATTRIB = 4

public export
IN_CLOSE_WRITE : InotifyMask
IN_CLOSE_WRITE = 8

public export
IN_CLOSE_NOWRITE : InotifyMask
IN_CLOSE_NOWRITE = 16

public export
IN_CREATE : InotifyMask
IN_CREATE = 256

public export
IN_DELETE : InotifyMask
IN_DELETE = 512

public export
IN_DELETE_SELF : InotifyMask
IN_DELETE_SELF = 1024

public export
IN_MODIFY : InotifyMask
IN_MODIFY = 2

public export
IN_MOVE_SELF : InotifyMask
IN_MOVE_SELF = 2048

public export
IN_MOVED_FROM : InotifyMask
IN_MOVED_FROM = 64

public export
IN_MOVED_TO : InotifyMask
IN_MOVED_TO = 128

public export
IN_OPEN : InotifyMask
IN_OPEN = 32

public export
IN_ALL_EVENTS : InotifyMask
IN_ALL_EVENTS = 4095

public export
IN_MOVE : InotifyMask
IN_MOVE = 192

public export
IN_CLOSE : InotifyMask
IN_CLOSE = 24

public export
IN_DONT_FOLLOW : InotifyMask
IN_DONT_FOLLOW = 33554432

public export
IN_EXCL_UNLINK : InotifyMask
IN_EXCL_UNLINK = 67108864

public export
IN_MASK_ADD : InotifyMask
IN_MASK_ADD = 536870912

public export
IN_ONESHOT : InotifyMask
IN_ONESHOT = -2147483648

public export
IN_ONLYDIR : InotifyMask
IN_ONLYDIR = 16777216

public export
IN_MASK_CREATE : InotifyMask
IN_MASK_CREATE = 268435456

public export
IN_IGNORED : InotifyMask
IN_IGNORED = 32768

public export
IN_ISDIR : InotifyMask
IN_ISDIR = 1073741824

public export
IN_Q_OVERFLOW : InotifyMask
IN_Q_OVERFLOW = 16384

public export
IN_UNMOUNT : InotifyMask
IN_UNMOUNT = 8192
