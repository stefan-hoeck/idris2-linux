-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Linux.Limits

import Data.C.Integer

%default total

export %foreign "C:sysconf, linux-idris"
sysconf : Bits32 -> Long

export %foreign "C:pathconf, linux-idris"
pathconf : String -> Bits32 -> Long

export %foreign "C:fpathconf, linux-idris"
fpathconf : Bits32 -> Bits32 -> Long

public export
SC_ARG_MAX : Bits32
SC_ARG_MAX = 0

public export
SC_CHILD_MAX : Bits32
SC_CHILD_MAX = 1

public export
SC_HOST_NAME_MAX : Bits32
SC_HOST_NAME_MAX = 180

public export
SC_LOGIN_NAME_MAX : Bits32
SC_LOGIN_NAME_MAX = 71

public export
SC_NGROUPS_MAX : Bits32
SC_NGROUPS_MAX = 3

public export
SC_CLK_TCK : Bits32
SC_CLK_TCK = 2

public export
SC_OPEN_MAX : Bits32
SC_OPEN_MAX = 4

public export
SC_PAGESIZE : Bits32
SC_PAGESIZE = 30

public export
SC_PAGE_SIZE : Bits32
SC_PAGE_SIZE = 30

public export
SC_RE_DUP_MAX : Bits32
SC_RE_DUP_MAX = 44

public export
SC_STREAM_MAX : Bits32
SC_STREAM_MAX = 5

public export
SC_SYMLOOP_MAX : Bits32
SC_SYMLOOP_MAX = 173

public export
SC_TTY_NAME_MAX : Bits32
SC_TTY_NAME_MAX = 72

public export
SC_TZNAME_MAX : Bits32
SC_TZNAME_MAX = 6

public export
SC_VERSION : Bits32
SC_VERSION = 29

public export
SC_BC_BASE_MAX : Bits32
SC_BC_BASE_MAX = 36

public export
SC_BC_DIM_MAX : Bits32
SC_BC_DIM_MAX = 37

public export
SC_BC_SCALE_MAX : Bits32
SC_BC_SCALE_MAX = 38

public export
SC_BC_STRING_MAX : Bits32
SC_BC_STRING_MAX = 39

public export
SC_COLL_WEIGHTS_MAX : Bits32
SC_COLL_WEIGHTS_MAX = 40

public export
SC_EXPR_NEST_MAX : Bits32
SC_EXPR_NEST_MAX = 42

public export
SC_RTSIG_MAX : Bits32
SC_RTSIG_MAX = 31

public export
SC_SIGQUEUE_MAX : Bits32
SC_SIGQUEUE_MAX = 34

public export
SC_LINE_MAX : Bits32
SC_LINE_MAX = 43

public export
SC_2_VERSION : Bits32
SC_2_VERSION = 46

public export
SC_2_C_DEV : Bits32
SC_2_C_DEV = 48

public export
SC_2_FORT_DEV : Bits32
SC_2_FORT_DEV = 49

public export
SC_2_FORT_RUN : Bits32
SC_2_FORT_RUN = 50

public export
SC_2_LOCALEDEF : Bits32
SC_2_LOCALEDEF = 52

public export
SC_2_SW_DEV : Bits32
SC_2_SW_DEV = 51

public export
PC_LINK_MAX : Bits32
PC_LINK_MAX = 0

public export
PC_MAX_CANON : Bits32
PC_MAX_CANON = 1

public export
PC_MAX_INPUT : Bits32
PC_MAX_INPUT = 2

public export
PC_NAME_MAX : Bits32
PC_NAME_MAX = 3

public export
PC_PATH_MAX : Bits32
PC_PATH_MAX = 4

public export
PC_PIPE_BUF : Bits32
PC_PIPE_BUF = 5

public export
PC_CHOWN_RESTRICTED : Bits32
PC_CHOWN_RESTRICTED = 6

public export
PC_NO_TRUNC : Bits32
PC_NO_TRUNC = 7

public export
PC_VDISABLE : Bits32
PC_VDISABLE = 8
