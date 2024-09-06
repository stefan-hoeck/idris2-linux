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

public export
SIGHUP : Signal
SIGHUP = 1

public export
SIGINT : Signal
SIGINT = 2

public export
SIGQUIT : Signal
SIGQUIT = 3

public export
SIGILL : Signal
SIGILL = 4

public export
SIGTRAP : Signal
SIGTRAP = 5

public export
SIGABRT : Signal
SIGABRT = 6

public export
SIGBUS : Signal
SIGBUS = 7

public export
SIGFPE : Signal
SIGFPE = 8

public export
SIGKILL : Signal
SIGKILL = 9

public export
SIGUSR1 : Signal
SIGUSR1 = 10

public export
SIGSEGV : Signal
SIGSEGV = 11

public export
SIGUSR2 : Signal
SIGUSR2 = 12

public export
SIGPIPE : Signal
SIGPIPE = 13

public export
SIGALRM : Signal
SIGALRM = 14

public export
SIGTERM : Signal
SIGTERM = 15

public export
SIGCHLD : Signal
SIGCHLD = 17

public export
SIGCONT : Signal
SIGCONT = 18

public export
SIGSTOP : Signal
SIGSTOP = 19

public export
SIGTSTP : Signal
SIGTSTP = 20

public export
SIGTTIN : Signal
SIGTTIN = 21

public export
SIGTTOU : Signal
SIGTTOU = 22

public export
SIGURG : Signal
SIGURG = 23

public export
SIGXCPU : Signal
SIGXCPU = 24

public export
SIGXFSZ : Signal
SIGXFSZ = 25

public export
SIGVTALRM : Signal
SIGVTALRM = 26

public export
SIGPROF : Signal
SIGPROF = 27

public export
SIGPOLL : Signal
SIGPOLL = 29

public export
SIGSYS : Signal
SIGSYS = 31
