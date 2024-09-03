-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Posix.Errno.Type

import Derive.Finite
import Derive.Prelude

%default total
%language ElabReflection

public export
data Errno : Type where
  EPERM : Errno
  ENOENT : Errno
  ESRCH : Errno
  EINTR : Errno
  EIO : Errno
  ENXIO : Errno
  E2BIG : Errno
  ENOEXEC : Errno
  EBADF : Errno
  ECHILD : Errno
  EAGAIN : Errno
  ENOMEM : Errno
  EACCES : Errno
  EFAULT : Errno
  ENOTBLK : Errno
  EBUSY : Errno
  EEXIST : Errno
  EXDEV : Errno
  ENODEV : Errno
  ENOTDIR : Errno
  EISDIR : Errno
  EINVAL : Errno
  ENFILE : Errno
  EMFILE : Errno
  ENOTTY : Errno
  ETXTBSY : Errno
  EFBIG : Errno
  ENOSPC : Errno
  ESPIPE : Errno
  EROFS : Errno
  EMLINK : Errno
  EPIPE : Errno
  EDOM : Errno
  ERANGE : Errno
  EDEADLK : Errno
  ENAMETOOLONG : Errno
  ENOLCK : Errno
  ENOSYS : Errno
  ENOTEMPTY : Errno
  ELOOP : Errno
  ENOMSG : Errno
  EIDRM : Errno
  ECHRNG : Errno
  EL2NSYNC : Errno
  EL3HLT : Errno
  EL3RST : Errno
  ELNRNG : Errno
  EUNATCH : Errno
  ENOCSI : Errno
  EL2HLT : Errno
  EBADE : Errno
  EBADR : Errno
  EXFULL : Errno
  ENOANO : Errno
  EBADRQC : Errno
  EBADSLT : Errno
  EDEADLOCK : Errno
  EBFONT : Errno
  ENOSTR : Errno
  ENODATA : Errno
  ETIME : Errno
  ENOSR : Errno
  ENONET : Errno
  ENOPKG : Errno
  EREMOTE : Errno
  ENOLINK : Errno
  EADV : Errno
  ESRMNT : Errno
  ECOMM : Errno
  EPROTO : Errno
  EMULTIHOP : Errno
  EDOTDOT : Errno
  EBADMSG : Errno
  EOVERFLOW : Errno
  ENOTUNIQ : Errno
  EBADFD : Errno
  EREMCHG : Errno
  ELIBACC : Errno
  ELIBBAD : Errno
  ELIBSCN : Errno
  ELIBMAX : Errno
  ELIBEXEC : Errno
  EILSEQ : Errno
  ERESTART : Errno
  ESTRPIPE : Errno
  EUSERS : Errno
  ENOTSOCK : Errno
  EDESTADDRREQ : Errno
  EMSGSIZE : Errno
  EPROTOTYPE : Errno
  ENOPROTOOPT : Errno
  EPROTONOSUPPORT : Errno
  ESOCKTNOSUPPORT : Errno
  EOPNOTSUPP : Errno
  EPFNOSUPPORT : Errno
  EAFNOSUPPORT : Errno
  EADDRINUSE : Errno
  EADDRNOTAVAIL : Errno
  ENETDOWN : Errno
  ENETUNREACH : Errno
  ENETRESET : Errno
  ECONNABORTED : Errno
  ECONNRESET : Errno
  ENOBUFS : Errno
  EISCONN : Errno
  ENOTCONN : Errno
  ESHUTDOWN : Errno
  ETOOMANYREFS : Errno
  ETIMEDOUT : Errno
  ECONNREFUSED : Errno
  EHOSTDOWN : Errno
  EHOSTUNREACH : Errno
  EALREADY : Errno
  EINPROGRESS : Errno
  ESTALE : Errno
  EUCLEAN : Errno
  ENOTNAM : Errno
  ENAVAIL : Errno
  EISNAM : Errno
  EREMOTEIO : Errno
  EDQUOT : Errno
  ENOMEDIUM : Errno
  EMEDIUMTYPE : Errno
  ECANCELED : Errno
  ENOKEY : Errno
  EKEYEXPIRED : Errno
  EKEYREVOKED : Errno
  EKEYREJECTED : Errno
  EOWNERDEAD : Errno
  ENOTRECOVERABLE : Errno
  ERFKILL : Errno
  EHWPOISON : Errno
  EOTHER : Errno

%runElab derive "Errno" [Show,Eq,Ord,Finite]

public export
errorCode : Errno -> Bits32
errorCode EPERM = 1
errorCode ENOENT = 2
errorCode ESRCH = 3
errorCode EINTR = 4
errorCode EIO = 5
errorCode ENXIO = 6
errorCode E2BIG = 7
errorCode ENOEXEC = 8
errorCode EBADF = 9
errorCode ECHILD = 10
errorCode EAGAIN = 11
errorCode ENOMEM = 12
errorCode EACCES = 13
errorCode EFAULT = 14
errorCode ENOTBLK = 15
errorCode EBUSY = 16
errorCode EEXIST = 17
errorCode EXDEV = 18
errorCode ENODEV = 19
errorCode ENOTDIR = 20
errorCode EISDIR = 21
errorCode EINVAL = 22
errorCode ENFILE = 23
errorCode EMFILE = 24
errorCode ENOTTY = 25
errorCode ETXTBSY = 26
errorCode EFBIG = 27
errorCode ENOSPC = 28
errorCode ESPIPE = 29
errorCode EROFS = 30
errorCode EMLINK = 31
errorCode EPIPE = 32
errorCode EDOM = 33
errorCode ERANGE = 34
errorCode EDEADLK = 35
errorCode ENAMETOOLONG = 36
errorCode ENOLCK = 37
errorCode ENOSYS = 38
errorCode ENOTEMPTY = 39
errorCode ELOOP = 40
errorCode ENOMSG = 42
errorCode EIDRM = 43
errorCode ECHRNG = 44
errorCode EL2NSYNC = 45
errorCode EL3HLT = 46
errorCode EL3RST = 47
errorCode ELNRNG = 48
errorCode EUNATCH = 49
errorCode ENOCSI = 50
errorCode EL2HLT = 51
errorCode EBADE = 52
errorCode EBADR = 53
errorCode EXFULL = 54
errorCode ENOANO = 55
errorCode EBADRQC = 56
errorCode EBADSLT = 57
errorCode EDEADLOCK = 35
errorCode EBFONT = 59
errorCode ENOSTR = 60
errorCode ENODATA = 61
errorCode ETIME = 62
errorCode ENOSR = 63
errorCode ENONET = 64
errorCode ENOPKG = 65
errorCode EREMOTE = 66
errorCode ENOLINK = 67
errorCode EADV = 68
errorCode ESRMNT = 69
errorCode ECOMM = 70
errorCode EPROTO = 71
errorCode EMULTIHOP = 72
errorCode EDOTDOT = 73
errorCode EBADMSG = 74
errorCode EOVERFLOW = 75
errorCode ENOTUNIQ = 76
errorCode EBADFD = 77
errorCode EREMCHG = 78
errorCode ELIBACC = 79
errorCode ELIBBAD = 80
errorCode ELIBSCN = 81
errorCode ELIBMAX = 82
errorCode ELIBEXEC = 83
errorCode EILSEQ = 84
errorCode ERESTART = 85
errorCode ESTRPIPE = 86
errorCode EUSERS = 87
errorCode ENOTSOCK = 88
errorCode EDESTADDRREQ = 89
errorCode EMSGSIZE = 90
errorCode EPROTOTYPE = 91
errorCode ENOPROTOOPT = 92
errorCode EPROTONOSUPPORT = 93
errorCode ESOCKTNOSUPPORT = 94
errorCode EOPNOTSUPP = 95
errorCode EPFNOSUPPORT = 96
errorCode EAFNOSUPPORT = 97
errorCode EADDRINUSE = 98
errorCode EADDRNOTAVAIL = 99
errorCode ENETDOWN = 100
errorCode ENETUNREACH = 101
errorCode ENETRESET = 102
errorCode ECONNABORTED = 103
errorCode ECONNRESET = 104
errorCode ENOBUFS = 105
errorCode EISCONN = 106
errorCode ENOTCONN = 107
errorCode ESHUTDOWN = 108
errorCode ETOOMANYREFS = 109
errorCode ETIMEDOUT = 110
errorCode ECONNREFUSED = 111
errorCode EHOSTDOWN = 112
errorCode EHOSTUNREACH = 113
errorCode EALREADY = 114
errorCode EINPROGRESS = 115
errorCode ESTALE = 116
errorCode EUCLEAN = 117
errorCode ENOTNAM = 118
errorCode ENAVAIL = 119
errorCode EISNAM = 120
errorCode EREMOTEIO = 121
errorCode EDQUOT = 122
errorCode ENOMEDIUM = 123
errorCode EMEDIUMTYPE = 124
errorCode ECANCELED = 125
errorCode ENOKEY = 126
errorCode EKEYEXPIRED = 127
errorCode EKEYREVOKED = 128
errorCode EKEYREJECTED = 129
errorCode EOWNERDEAD = 130
errorCode ENOTRECOVERABLE = 131
errorCode ERFKILL = 132
errorCode EHWPOISON = 133
errorCode EOTHER = 0

export
errorText : Errno -> String
errorText EPERM = "Operation not permitted"
errorText ENOENT = "No such file or directory"
errorText ESRCH = "No such process"
errorText EINTR = "Interrupted system call"
errorText EIO = "Input/output error"
errorText ENXIO = "No such device or address"
errorText E2BIG = "Argument list too long"
errorText ENOEXEC = "Exec format error"
errorText EBADF = "Bad file descriptor"
errorText ECHILD = "No child processes"
errorText EAGAIN = "Resource temporarily unavailable"
errorText ENOMEM = "Cannot allocate memory"
errorText EACCES = "Permission denied"
errorText EFAULT = "Bad address"
errorText ENOTBLK = "Block device required"
errorText EBUSY = "Device or resource busy"
errorText EEXIST = "File exists"
errorText EXDEV = "Invalid cross-device link"
errorText ENODEV = "No such device"
errorText ENOTDIR = "Not a directory"
errorText EISDIR = "Is a directory"
errorText EINVAL = "Invalid argument"
errorText ENFILE = "Too many open files in system"
errorText EMFILE = "Too many open files"
errorText ENOTTY = "Inappropriate ioctl for device"
errorText ETXTBSY = "Text file busy"
errorText EFBIG = "File too large"
errorText ENOSPC = "No space left on device"
errorText ESPIPE = "Illegal seek"
errorText EROFS = "Read-only file system"
errorText EMLINK = "Too many links"
errorText EPIPE = "Broken pipe"
errorText EDOM = "Numerical argument out of domain"
errorText ERANGE = "Numerical result out of range"
errorText EDEADLK = "Resource deadlock avoided"
errorText ENAMETOOLONG = "File name too long"
errorText ENOLCK = "No locks available"
errorText ENOSYS = "Function not implemented"
errorText ENOTEMPTY = "Directory not empty"
errorText ELOOP = "Too many levels of symbolic links"
errorText ENOMSG = "No message of desired type"
errorText EIDRM = "Identifier removed"
errorText ECHRNG = "Channel number out of range"
errorText EL2NSYNC = "Level 2 not synchronized"
errorText EL3HLT = "Level 3 halted"
errorText EL3RST = "Level 3 reset"
errorText ELNRNG = "Link number out of range"
errorText EUNATCH = "Protocol driver not attached"
errorText ENOCSI = "No CSI structure available"
errorText EL2HLT = "Level 2 halted"
errorText EBADE = "Invalid exchange"
errorText EBADR = "Invalid request descriptor"
errorText EXFULL = "Exchange full"
errorText ENOANO = "No anode"
errorText EBADRQC = "Invalid request code"
errorText EBADSLT = "Invalid slot"
errorText EDEADLOCK = "Resource deadlock avoided"
errorText EBFONT = "Bad font file format"
errorText ENOSTR = "Device not a stream"
errorText ENODATA = "No data available"
errorText ETIME = "Timer expired"
errorText ENOSR = "Out of streams resources"
errorText ENONET = "Machine is not on the network"
errorText ENOPKG = "Package not installed"
errorText EREMOTE = "Object is remote"
errorText ENOLINK = "Link has been severed"
errorText EADV = "Advertise error"
errorText ESRMNT = "Srmount error"
errorText ECOMM = "Communication error on send"
errorText EPROTO = "Protocol error"
errorText EMULTIHOP = "Multihop attempted"
errorText EDOTDOT = "RFS specific error"
errorText EBADMSG = "Bad message"
errorText EOVERFLOW = "Value too large for defined data type"
errorText ENOTUNIQ = "Name not unique on network"
errorText EBADFD = "File descriptor in bad state"
errorText EREMCHG = "Remote address changed"
errorText ELIBACC = "Can not access a needed shared library"
errorText ELIBBAD = "Accessing a corrupted shared library"
errorText ELIBSCN = ".lib section in a.out corrupted"
errorText ELIBMAX = "Attempting to link in too many shared libraries"
errorText ELIBEXEC = "Cannot exec a shared library directly"
errorText EILSEQ = "Invalid or incomplete multibyte or wide character"
errorText ERESTART = "Interrupted system call should be restarted"
errorText ESTRPIPE = "Streams pipe error"
errorText EUSERS = "Too many users"
errorText ENOTSOCK = "Socket operation on non-socket"
errorText EDESTADDRREQ = "Destination address required"
errorText EMSGSIZE = "Message too long"
errorText EPROTOTYPE = "Protocol wrong type for socket"
errorText ENOPROTOOPT = "Protocol not available"
errorText EPROTONOSUPPORT = "Protocol not supported"
errorText ESOCKTNOSUPPORT = "Socket type not supported"
errorText EOPNOTSUPP = "Operation not supported"
errorText EPFNOSUPPORT = "Protocol family not supported"
errorText EAFNOSUPPORT = "Address family not supported by protocol"
errorText EADDRINUSE = "Address already in use"
errorText EADDRNOTAVAIL = "Cannot assign requested address"
errorText ENETDOWN = "Network is down"
errorText ENETUNREACH = "Network is unreachable"
errorText ENETRESET = "Network dropped connection on reset"
errorText ECONNABORTED = "Software caused connection abort"
errorText ECONNRESET = "Connection reset by peer"
errorText ENOBUFS = "No buffer space available"
errorText EISCONN = "Transport endpoint is already connected"
errorText ENOTCONN = "Transport endpoint is not connected"
errorText ESHUTDOWN = "Cannot send after transport endpoint shutdown"
errorText ETOOMANYREFS = "Too many references: cannot splice"
errorText ETIMEDOUT = "Connection timed out"
errorText ECONNREFUSED = "Connection refused"
errorText EHOSTDOWN = "Host is down"
errorText EHOSTUNREACH = "No route to host"
errorText EALREADY = "Operation already in progress"
errorText EINPROGRESS = "Operation now in progress"
errorText ESTALE = "Stale file handle"
errorText EUCLEAN = "Structure needs cleaning"
errorText ENOTNAM = "Not a XENIX named type file"
errorText ENAVAIL = "No XENIX semaphores available"
errorText EISNAM = "Is a named type file"
errorText EREMOTEIO = "Remote I/O error"
errorText EDQUOT = "Disk quota exceeded"
errorText ENOMEDIUM = "No medium found"
errorText EMEDIUMTYPE = "Wrong medium type"
errorText ECANCELED = "Operation canceled"
errorText ENOKEY = "Required key not available"
errorText EKEYEXPIRED = "Key has expired"
errorText EKEYREVOKED = "Key has been revoked"
errorText EKEYREJECTED = "Key was rejected by service"
errorText EOWNERDEAD = "Owner died"
errorText ENOTRECOVERABLE = "State not recoverable"
errorText ERFKILL = "Operation not possible due to RF-kill"
errorText EHWPOISON = "Memory page has hardware error"
errorText EOTHER = "Other (unknown) error"
