-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Posix.Socket.Types

import Data.Bits
import Data.C.Integer
import Derive.Finite
import Derive.Prelude

%default total
%language ElabReflection

public export
data Domain : Type where
  AF_UNIX  : Domain
  AF_INET  : Domain
  AF_INET6 : Domain

%runElab derive "Domain" [Show,Eq,Ord,Finite]

public export
record SockType where
  constructor ST
  type : Bits32

%runElab derive "SockType" [Show,Eq,Ord,FromInteger]

public export
Semigroup SockType where
  ST x <+> ST y = ST $ x .|. y

public export
record SockFlags where
  constructor SF
  flags : Bits32

namespace SockFlags
  %runElab derive "SockFlags" [Show,Eq,Ord,FromInteger]

public export
Semigroup SockFlags where
  SF x <+> SF y = SF $ x .|. y

public export
domainCode : Domain -> Bits8
domainCode AF_UNIX  = 1
domainCode AF_INET  = 2
domainCode AF_INET6 = 10

public export
SOCK_STREAM : SockType
SOCK_STREAM = 1

public export
SOCK_DGRAM : SockType
SOCK_DGRAM = 2

public export
SOCK_RAW : SockType
SOCK_RAW = 3

public export
SOCK_NONBLOCK : SockType
SOCK_NONBLOCK = 2048

public export
SOCK_CLOEXEC : SockType
SOCK_CLOEXEC = 524288

public export
MSG_DONTWAIT : SockFlags
MSG_DONTWAIT = 64

public export
MSG_OOB : SockFlags
MSG_OOB = 1

public export
MSG_PEEK : SockFlags
MSG_PEEK = 2

public export
MSG_WAITALL : SockFlags
MSG_WAITALL = 256

public export
MSG_NOSIGNAL : SockFlags
MSG_NOSIGNAL = 16384

public export
sockaddr_un_size : Bits32
sockaddr_un_size = 110

public export
sockaddr_in_size : Bits32
sockaddr_in_size = 16

public export
sockaddr_in6_size : Bits32
sockaddr_in6_size = 28
