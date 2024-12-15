-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Linux.Epoll.Flags

import Data.Bits
import Derive.Prelude

%default total
%language ElabReflection

public export
record Event where
  constructor E
  event : Bits32

%runElab derive "Event" [Show,Eq,Ord,FromInteger]

public export
Semigroup Event where
  E x <+> E y = E $ x .|. y

public export
Monoid Event where neutral = E 0

public export
record EpollFlags where
  constructor F
  flags : Bits32

namespace EpollFlags
  %runElab derive "EpollFlags" [Show,Eq,Ord,FromInteger]

public export
Semigroup EpollFlags where
  F x <+> F y = F $ x .|. y

public export
Monoid EpollFlags where neutral = F 0

public export
EPOLLIN : Event
EPOLLIN = 1

public export
EPOLLOUT : Event
EPOLLOUT = 4

public export
EPOLLRDHUP : Event
EPOLLRDHUP = 8192

public export
EPOLLPRI : Event
EPOLLPRI = 2

public export
EPOLLERR : Event
EPOLLERR = 8

public export
EPOLLHUP : Event
EPOLLHUP = 16

public export
EPOLLET : EpollFlags
EPOLLET = 2147483648

public export
EPOLLONESHOT : EpollFlags
EPOLLONESHOT = 1073741824

public export
EPOLLWAKEUP : EpollFlags
EPOLLWAKEUP = 536870912

public export
EPOLLEXCLUSIVE : EpollFlags
EPOLLEXCLUSIVE = 268435456
