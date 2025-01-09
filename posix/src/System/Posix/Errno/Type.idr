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
record Errno where
  constructor EN
  errno : Bits32

%runElab derive "Errno" [Show,Eq,Ord,FromInteger]


public export %inline
EPERM : Errno
EPERM = 1

public export %inline
ENOENT : Errno
ENOENT = 2

public export %inline
ESRCH : Errno
ESRCH = 3

public export %inline
EINTR : Errno
EINTR = 4

public export %inline
EIO : Errno
EIO = 5

public export %inline
ENXIO : Errno
ENXIO = 6

public export %inline
E2BIG : Errno
E2BIG = 7

public export %inline
ENOEXEC : Errno
ENOEXEC = 8

public export %inline
EBADF : Errno
EBADF = 9

public export %inline
ECHILD : Errno
ECHILD = 10

public export %inline
EAGAIN : Errno
EAGAIN = 11

public export %inline
EWOULDBLOCK : Errno
EWOULDBLOCK = 11

public export %inline
ENOMEM : Errno
ENOMEM = 12

public export %inline
EACCES : Errno
EACCES = 13

public export %inline
EFAULT : Errno
EFAULT = 14

public export %inline
ENOTBLK : Errno
ENOTBLK = 15

public export %inline
EBUSY : Errno
EBUSY = 16

public export %inline
EEXIST : Errno
EEXIST = 17

public export %inline
EXDEV : Errno
EXDEV = 18

public export %inline
ENODEV : Errno
ENODEV = 19

public export %inline
ENOTDIR : Errno
ENOTDIR = 20

public export %inline
EISDIR : Errno
EISDIR = 21

public export %inline
EINVAL : Errno
EINVAL = 22

public export %inline
ENFILE : Errno
ENFILE = 23

public export %inline
EMFILE : Errno
EMFILE = 24

public export %inline
ENOTTY : Errno
ENOTTY = 25

public export %inline
ETXTBSY : Errno
ETXTBSY = 26

public export %inline
EFBIG : Errno
EFBIG = 27

public export %inline
ENOSPC : Errno
ENOSPC = 28

public export %inline
ESPIPE : Errno
ESPIPE = 29

public export %inline
EROFS : Errno
EROFS = 30

public export %inline
EMLINK : Errno
EMLINK = 31

public export %inline
EPIPE : Errno
EPIPE = 32

public export %inline
EDOM : Errno
EDOM = 33

public export %inline
ERANGE : Errno
ERANGE = 34

public export %inline
EDEADLK : Errno
EDEADLK = 35

public export %inline
ENAMETOOLONG : Errno
ENAMETOOLONG = 36

public export %inline
ENOLCK : Errno
ENOLCK = 37

public export %inline
ENOSYS : Errno
ENOSYS = 38

public export %inline
ENOTEMPTY : Errno
ENOTEMPTY = 39

public export %inline
ELOOP : Errno
ELOOP = 40

public export %inline
ENOMSG : Errno
ENOMSG = 42

public export %inline
EIDRM : Errno
EIDRM = 43

public export %inline
ENOSTR : Errno
ENOSTR = 60

public export %inline
ENODATA : Errno
ENODATA = 61

public export %inline
ETIME : Errno
ETIME = 62

public export %inline
ENOSR : Errno
ENOSR = 63

public export %inline
EREMOTE : Errno
EREMOTE = 66

public export %inline
ENOLINK : Errno
ENOLINK = 67

public export %inline
EPROTO : Errno
EPROTO = 71

public export %inline
EMULTIHOP : Errno
EMULTIHOP = 72

public export %inline
EBADMSG : Errno
EBADMSG = 74

public export %inline
EOVERFLOW : Errno
EOVERFLOW = 75

public export %inline
EILSEQ : Errno
EILSEQ = 84

public export %inline
EUSERS : Errno
EUSERS = 87

public export %inline
ENOTSOCK : Errno
ENOTSOCK = 88

public export %inline
EDESTADDRREQ : Errno
EDESTADDRREQ = 89

public export %inline
EMSGSIZE : Errno
EMSGSIZE = 90

public export %inline
EPROTOTYPE : Errno
EPROTOTYPE = 91

public export %inline
ENOPROTOOPT : Errno
ENOPROTOOPT = 92

public export %inline
EPROTONOSUPPORT : Errno
EPROTONOSUPPORT = 93

public export %inline
ESOCKTNOSUPPORT : Errno
ESOCKTNOSUPPORT = 94

public export %inline
EOPNOTSUPP : Errno
EOPNOTSUPP = 95

public export %inline
EPFNOSUPPORT : Errno
EPFNOSUPPORT = 96

public export %inline
EAFNOSUPPORT : Errno
EAFNOSUPPORT = 97

public export %inline
EADDRINUSE : Errno
EADDRINUSE = 98

public export %inline
EADDRNOTAVAIL : Errno
EADDRNOTAVAIL = 99

public export %inline
ENETDOWN : Errno
ENETDOWN = 100

public export %inline
ENETUNREACH : Errno
ENETUNREACH = 101

public export %inline
ENETRESET : Errno
ENETRESET = 102

public export %inline
ECONNABORTED : Errno
ECONNABORTED = 103

public export %inline
ECONNRESET : Errno
ECONNRESET = 104

public export %inline
ENOBUFS : Errno
ENOBUFS = 105

public export %inline
EISCONN : Errno
EISCONN = 106

public export %inline
ENOTCONN : Errno
ENOTCONN = 107

public export %inline
ESHUTDOWN : Errno
ESHUTDOWN = 108

public export %inline
ETOOMANYREFS : Errno
ETOOMANYREFS = 109

public export %inline
ETIMEDOUT : Errno
ETIMEDOUT = 110

public export %inline
ECONNREFUSED : Errno
ECONNREFUSED = 111

public export %inline
EHOSTDOWN : Errno
EHOSTDOWN = 112

public export %inline
EHOSTUNREACH : Errno
EHOSTUNREACH = 113

public export %inline
EALREADY : Errno
EALREADY = 114

public export %inline
EINPROGRESS : Errno
EINPROGRESS = 115

public export %inline
ESTALE : Errno
ESTALE = 116

public export %inline
EDQUOT : Errno
EDQUOT = 122

public export %inline
ECANCELED : Errno
ECANCELED = 125

public export %inline
EOWNERDEAD : Errno
EOWNERDEAD = 130

public export %inline
ENOTRECOVERABLE : Errno
ENOTRECOVERABLE = 131

public export %inline
ECHRNG : Errno
ECHRNG = 44

public export %inline
EL2NSYNC : Errno
EL2NSYNC = 45

public export %inline
EL3HLT : Errno
EL3HLT = 46

public export %inline
EL3RST : Errno
EL3RST = 47

public export %inline
ELNRNG : Errno
ELNRNG = 48

public export %inline
EUNATCH : Errno
EUNATCH = 49

public export %inline
ENOCSI : Errno
ENOCSI = 50

public export %inline
EL2HLT : Errno
EL2HLT = 51

public export %inline
EBADE : Errno
EBADE = 52

public export %inline
EBADR : Errno
EBADR = 53

public export %inline
EXFULL : Errno
EXFULL = 54

public export %inline
ENOANO : Errno
ENOANO = 55

public export %inline
EBADRQC : Errno
EBADRQC = 56

public export %inline
EBADSLT : Errno
EBADSLT = 57

public export %inline
EBFONT : Errno
EBFONT = 59

public export %inline
ENONET : Errno
ENONET = 64

public export %inline
ENOPKG : Errno
ENOPKG = 65

public export %inline
EADV : Errno
EADV = 68

public export %inline
ESRMNT : Errno
ESRMNT = 69

public export %inline
ECOMM : Errno
ECOMM = 70

public export %inline
EDOTDOT : Errno
EDOTDOT = 73

public export %inline
ENOTUNIQ : Errno
ENOTUNIQ = 76

public export %inline
EBADFD : Errno
EBADFD = 77

public export %inline
EREMCHG : Errno
EREMCHG = 78

public export %inline
ELIBACC : Errno
ELIBACC = 79

public export %inline
ELIBBAD : Errno
ELIBBAD = 80

public export %inline
ELIBSCN : Errno
ELIBSCN = 81

public export %inline
ELIBMAX : Errno
ELIBMAX = 82

public export %inline
ELIBEXEC : Errno
ELIBEXEC = 83

public export %inline
ERESTART : Errno
ERESTART = 85

public export %inline
ESTRPIPE : Errno
ESTRPIPE = 86

public export %inline
EUCLEAN : Errno
EUCLEAN = 117

public export %inline
ENOTNAM : Errno
ENOTNAM = 118

public export %inline
ENAVAIL : Errno
ENAVAIL = 119

public export %inline
EISNAM : Errno
EISNAM = 120

public export %inline
EREMOTEIO : Errno
EREMOTEIO = 121

public export %inline
ENOMEDIUM : Errno
ENOMEDIUM = 123

public export %inline
EMEDIUMTYPE : Errno
EMEDIUMTYPE = 124

public export %inline
ENOKEY : Errno
ENOKEY = 126

public export %inline
EKEYEXPIRED : Errno
EKEYEXPIRED = 127

public export %inline
EKEYREVOKED : Errno
EKEYREVOKED = 128

public export %inline
EKEYREJECTED : Errno
EKEYREJECTED = 129

public export %inline
ERFKILL : Errno
ERFKILL = 132

public export %inline
EHWPOISON : Errno
EHWPOISON = 133

export
errorText : Errno -> String
errorText 1 = "Operation not permitted"
errorText 2 = "No such file or directory"
errorText 3 = "No such process"
errorText 4 = "Interrupted system call"
errorText 5 = "Input/output error"
errorText 6 = "No such device or address"
errorText 7 = "Argument list too long"
errorText 8 = "Exec format error"
errorText 9 = "Bad file descriptor"
errorText 10 = "No child processes"
errorText 11 = "Resource temporarily unavailable"
errorText 12 = "Cannot allocate memory"
errorText 13 = "Permission denied"
errorText 14 = "Bad address"
errorText 15 = "Block device required"
errorText 16 = "Device or resource busy"
errorText 17 = "File exists"
errorText 18 = "Invalid cross-device link"
errorText 19 = "No such device"
errorText 20 = "Not a directory"
errorText 21 = "Is a directory"
errorText 22 = "Invalid argument"
errorText 23 = "Too many open files in system"
errorText 24 = "Too many open files"
errorText 25 = "Inappropriate ioctl for device"
errorText 26 = "Text file busy"
errorText 27 = "File too large"
errorText 28 = "No space left on device"
errorText 29 = "Illegal seek"
errorText 30 = "Read-only file system"
errorText 31 = "Too many links"
errorText 32 = "Broken pipe"
errorText 33 = "Numerical argument out of domain"
errorText 34 = "Numerical result out of range"
errorText 35 = "Resource deadlock avoided"
errorText 36 = "File name too long"
errorText 37 = "No locks available"
errorText 38 = "Function not implemented"
errorText 39 = "Directory not empty"
errorText 40 = "Too many levels of symbolic links"
errorText 42 = "No message of desired type"
errorText 43 = "Identifier removed"
errorText 60 = "Device not a stream"
errorText 61 = "No data available"
errorText 62 = "Timer expired"
errorText 63 = "Out of streams resources"
errorText 66 = "Object is remote"
errorText 67 = "Link has been severed"
errorText 71 = "Protocol error"
errorText 72 = "Multihop attempted"
errorText 74 = "Bad message"
errorText 75 = "Value too large for defined data type"
errorText 84 = "Invalid or incomplete multibyte or wide character"
errorText 87 = "Too many users"
errorText 88 = "Socket operation on non-socket"
errorText 89 = "Destination address required"
errorText 90 = "Message too long"
errorText 91 = "Protocol wrong type for socket"
errorText 92 = "Protocol not available"
errorText 93 = "Protocol not supported"
errorText 94 = "Socket type not supported"
errorText 95 = "Operation not supported"
errorText 96 = "Protocol family not supported"
errorText 97 = "Address family not supported by protocol"
errorText 98 = "Address already in use"
errorText 99 = "Cannot assign requested address"
errorText 100 = "Network is down"
errorText 101 = "Network is unreachable"
errorText 102 = "Network dropped connection on reset"
errorText 103 = "Software caused connection abort"
errorText 104 = "Connection reset by peer"
errorText 105 = "No buffer space available"
errorText 106 = "Transport endpoint is already connected"
errorText 107 = "Transport endpoint is not connected"
errorText 108 = "Cannot send after transport endpoint shutdown"
errorText 109 = "Too many references: cannot splice"
errorText 110 = "Connection timed out"
errorText 111 = "Connection refused"
errorText 112 = "Host is down"
errorText 113 = "No route to host"
errorText 114 = "Operation already in progress"
errorText 115 = "Operation now in progress"
errorText 116 = "Stale file handle"
errorText 122 = "Disk quota exceeded"
errorText 125 = "Operation canceled"
errorText 130 = "Owner died"
errorText 131 = "State not recoverable"
errorText 44 = "Channel number out of range"
errorText 45 = "Level 2 not synchronized"
errorText 46 = "Level 3 halted"
errorText 47 = "Level 3 reset"
errorText 48 = "Link number out of range"
errorText 49 = "Protocol driver not attached"
errorText 50 = "No CSI structure available"
errorText 51 = "Level 2 halted"
errorText 52 = "Invalid exchange"
errorText 53 = "Invalid request descriptor"
errorText 54 = "Exchange full"
errorText 55 = "No anode"
errorText 56 = "Invalid request code"
errorText 57 = "Invalid slot"
errorText 59 = "Bad font file format"
errorText 64 = "Machine is not on the network"
errorText 65 = "Package not installed"
errorText 68 = "Advertise error"
errorText 69 = "Srmount error"
errorText 70 = "Communication error on send"
errorText 73 = "RFS specific error"
errorText 76 = "Name not unique on network"
errorText 77 = "File descriptor in bad state"
errorText 78 = "Remote address changed"
errorText 79 = "Can not access a needed shared library"
errorText 80 = "Accessing a corrupted shared library"
errorText 81 = ".lib section in a.out corrupted"
errorText 82 = "Attempting to link in too many shared libraries"
errorText 83 = "Cannot exec a shared library directly"
errorText 85 = "Interrupted system call should be restarted"
errorText 86 = "Streams pipe error"
errorText 117 = "Structure needs cleaning"
errorText 118 = "Not a XENIX named type file"
errorText 119 = "No XENIX semaphores available"
errorText 120 = "Is a named type file"
errorText 121 = "Remote I/O error"
errorText 123 = "No medium found"
errorText 124 = "Wrong medium type"
errorText 126 = "Required key not available"
errorText 127 = "Key has expired"
errorText 128 = "Key has been revoked"
errorText 129 = "Key was rejected by service"
errorText 132 = "Operation not possible due to RF-kill"
errorText 133 = "Memory page has hardware error"
errorText (EN x) = "Unknown error: \{show x}"

export
errorName : Errno -> String
errorName 1 = "EPERM"
errorName 2 = "ENOENT"
errorName 3 = "ESRCH"
errorName 4 = "EINTR"
errorName 5 = "EIO"
errorName 6 = "ENXIO"
errorName 7 = "E2BIG"
errorName 8 = "ENOEXEC"
errorName 9 = "EBADF"
errorName 10 = "ECHILD"
errorName 11 = "EAGAIN"
errorName 12 = "ENOMEM"
errorName 13 = "EACCES"
errorName 14 = "EFAULT"
errorName 15 = "ENOTBLK"
errorName 16 = "EBUSY"
errorName 17 = "EEXIST"
errorName 18 = "EXDEV"
errorName 19 = "ENODEV"
errorName 20 = "ENOTDIR"
errorName 21 = "EISDIR"
errorName 22 = "EINVAL"
errorName 23 = "ENFILE"
errorName 24 = "EMFILE"
errorName 25 = "ENOTTY"
errorName 26 = "ETXTBSY"
errorName 27 = "EFBIG"
errorName 28 = "ENOSPC"
errorName 29 = "ESPIPE"
errorName 30 = "EROFS"
errorName 31 = "EMLINK"
errorName 32 = "EPIPE"
errorName 33 = "EDOM"
errorName 34 = "ERANGE"
errorName 35 = "EDEADLK"
errorName 36 = "ENAMETOOLONG"
errorName 37 = "ENOLCK"
errorName 38 = "ENOSYS"
errorName 39 = "ENOTEMPTY"
errorName 40 = "ELOOP"
errorName 42 = "ENOMSG"
errorName 43 = "EIDRM"
errorName 60 = "ENOSTR"
errorName 61 = "ENODATA"
errorName 62 = "ETIME"
errorName 63 = "ENOSR"
errorName 66 = "EREMOTE"
errorName 67 = "ENOLINK"
errorName 71 = "EPROTO"
errorName 72 = "EMULTIHOP"
errorName 74 = "EBADMSG"
errorName 75 = "EOVERFLOW"
errorName 84 = "EILSEQ"
errorName 87 = "EUSERS"
errorName 88 = "ENOTSOCK"
errorName 89 = "EDESTADDRREQ"
errorName 90 = "EMSGSIZE"
errorName 91 = "EPROTOTYPE"
errorName 92 = "ENOPROTOOPT"
errorName 93 = "EPROTONOSUPPORT"
errorName 94 = "ESOCKTNOSUPPORT"
errorName 95 = "EOPNOTSUPP"
errorName 96 = "EPFNOSUPPORT"
errorName 97 = "EAFNOSUPPORT"
errorName 98 = "EADDRINUSE"
errorName 99 = "EADDRNOTAVAIL"
errorName 100 = "ENETDOWN"
errorName 101 = "ENETUNREACH"
errorName 102 = "ENETRESET"
errorName 103 = "ECONNABORTED"
errorName 104 = "ECONNRESET"
errorName 105 = "ENOBUFS"
errorName 106 = "EISCONN"
errorName 107 = "ENOTCONN"
errorName 108 = "ESHUTDOWN"
errorName 109 = "ETOOMANYREFS"
errorName 110 = "ETIMEDOUT"
errorName 111 = "ECONNREFUSED"
errorName 112 = "EHOSTDOWN"
errorName 113 = "EHOSTUNREACH"
errorName 114 = "EALREADY"
errorName 115 = "EINPROGRESS"
errorName 116 = "ESTALE"
errorName 122 = "EDQUOT"
errorName 125 = "ECANCELED"
errorName 130 = "EOWNERDEAD"
errorName 131 = "ENOTRECOVERABLE"
errorName 44 = "ECHRNG"
errorName 45 = "EL2NSYNC"
errorName 46 = "EL3HLT"
errorName 47 = "EL3RST"
errorName 48 = "ELNRNG"
errorName 49 = "EUNATCH"
errorName 50 = "ENOCSI"
errorName 51 = "EL2HLT"
errorName 52 = "EBADE"
errorName 53 = "EBADR"
errorName 54 = "EXFULL"
errorName 55 = "ENOANO"
errorName 56 = "EBADRQC"
errorName 57 = "EBADSLT"
errorName 59 = "EBFONT"
errorName 64 = "ENONET"
errorName 65 = "ENOPKG"
errorName 68 = "EADV"
errorName 69 = "ESRMNT"
errorName 70 = "ECOMM"
errorName 73 = "EDOTDOT"
errorName 76 = "ENOTUNIQ"
errorName 77 = "EBADFD"
errorName 78 = "EREMCHG"
errorName 79 = "ELIBACC"
errorName 80 = "ELIBBAD"
errorName 81 = "ELIBSCN"
errorName 82 = "ELIBMAX"
errorName 83 = "ELIBEXEC"
errorName 85 = "ERESTART"
errorName 86 = "ESTRPIPE"
errorName 117 = "EUCLEAN"
errorName 118 = "ENOTNAM"
errorName 119 = "ENAVAIL"
errorName 120 = "EISNAM"
errorName 121 = "EREMOTEIO"
errorName 123 = "ENOMEDIUM"
errorName 124 = "EMEDIUMTYPE"
errorName 126 = "ENOKEY"
errorName 127 = "EKEYEXPIRED"
errorName 128 = "EKEYREVOKED"
errorName 129 = "EKEYREJECTED"
errorName 132 = "ERFKILL"
errorName 133 = "EHWPOISON"
errorName (EN _) = "EUNKNOWN"
