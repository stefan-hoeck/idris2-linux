-- Note: This module is automatically generated when Idris builds
-- the library and the constants will be replaced with values
-- matching the system this is generated on.
--
-- The placeholders are here so that it works with tools like the LSP
-- without first compiling the library. They were generated on an x86_64
-- GNU/Linux system with GCC. If you are on a similar system, your numbers
-- might very well be identical.
module System.Posix.Signal.Types

import Data.Bits
import Data.C.Integer
import Data.SortedMap
import Derive.Prelude

%default total
%language ElabReflection

public export
data How : Type where
  SIG_BLOCK   : How
  SIG_UNBLOCK : How
  SIG_SETMASK : How

%runElab derive "How" [Show,Eq,Ord]

public export
record Signal where
  constructor S
  sig : Bits32

%runElab derive "Signal" [Show,Eq,Ord,FromInteger]


public export
howCode : How -> Bits8
howCode SIG_BLOCK   = 0
howCode SIG_UNBLOCK = 1
howCode SIG_SETMASK = 2

public export
SIGRTMIN : Signal
SIGRTMIN = 34

public export
SIGRTMAX : Signal
SIGRTMAX = 64

public export %inline
SIGHUP : Signal
SIGHUP = 1

public export %inline
SIGINT : Signal
SIGINT = 2

public export %inline
SIGQUIT : Signal
SIGQUIT = 3

public export %inline
SIGILL : Signal
SIGILL = 4

public export %inline
SIGTRAP : Signal
SIGTRAP = 5

public export %inline
SIGABRT : Signal
SIGABRT = 6

public export %inline
SIGBUS : Signal
SIGBUS = 7

public export %inline
SIGFPE : Signal
SIGFPE = 8

public export %inline
SIGKILL : Signal
SIGKILL = 9

public export %inline
SIGUSR1 : Signal
SIGUSR1 = 10

public export %inline
SIGSEGV : Signal
SIGSEGV = 11

public export %inline
SIGUSR2 : Signal
SIGUSR2 = 12

public export %inline
SIGPIPE : Signal
SIGPIPE = 13

public export %inline
SIGALRM : Signal
SIGALRM = 14

public export %inline
SIGTERM : Signal
SIGTERM = 15

public export %inline
SIGCHLD : Signal
SIGCHLD = 17

public export %inline
SIGCONT : Signal
SIGCONT = 18

public export %inline
SIGSTOP : Signal
SIGSTOP = 19

public export %inline
SIGTSTP : Signal
SIGTSTP = 20

public export %inline
SIGTTIN : Signal
SIGTTIN = 21

public export %inline
SIGTTOU : Signal
SIGTTOU = 22

public export %inline
SIGURG : Signal
SIGURG = 23

public export %inline
SIGXCPU : Signal
SIGXCPU = 24

public export %inline
SIGXFSZ : Signal
SIGXFSZ = 25

public export %inline
SIGVTALRM : Signal
SIGVTALRM = 26

public export %inline
SIGPROF : Signal
SIGPROF = 27

public export %inline
SIGPOLL : Signal
SIGPOLL = 29

public export %inline
SIGSYS : Signal
SIGSYS = 31

export
sigName : SortedMap Signal String
sigName =
  SortedMap.fromList
    [ (SIGHUP, "SIGHUP")
    , (SIGINT, "SIGINT")
    , (SIGQUIT, "SIGQUIT")
    , (SIGILL, "SIGILL")
    , (SIGTRAP, "SIGTRAP")
    , (SIGABRT, "SIGABRT")
    , (SIGBUS, "SIGBUS")
    , (SIGFPE, "SIGFPE")
    , (SIGKILL, "SIGKILL")
    , (SIGUSR1, "SIGUSR1")
    , (SIGSEGV, "SIGSEGV")
    , (SIGUSR2, "SIGUSR2")
    , (SIGPIPE, "SIGPIPE")
    , (SIGALRM, "SIGALRM")
    , (SIGTERM, "SIGTERM")
    , (SIGCHLD, "SIGCHLD")
    , (SIGCONT, "SIGCONT")
    , (SIGSTOP, "SIGSTOP")
    , (SIGTSTP, "SIGTSTP")
    , (SIGTTIN, "SIGTTIN")
    , (SIGTTOU, "SIGTTOU")
    , (SIGURG, "SIGURG")
    , (SIGXCPU, "SIGXCPU")
    , (SIGXFSZ, "SIGXFSZ")
    , (SIGVTALRM, "SIGVTALRM")
    , (SIGPROF, "SIGPROF")
    , (SIGPOLL, "SIGPOLL")
    , (SIGSYS, "SIGSYS")
    ]

public export %inline
siginfo_t_size : Nat
siginfo_t_size = 128
