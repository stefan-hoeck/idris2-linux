module System.Posix.Process.ProcStatus

import public Data.C.Ptr

import Derive.Prelude
import System.Posix.Errno
import System.Posix.Signal

%default total
%language ElabReflection

%foreign "C:li_wifexited, posix-idris"
exited : CInt -> Bits8

%foreign "C:li_wexitstatus, posix-idris"
exitstatus : CInt -> Bits8

%foreign "C:li_wifsignaled, posix-idris"
signaled : CInt -> Bits8

%foreign "C:li_wtermsig, posix-idris"
termsig : CInt -> Bits32

%foreign "C:li_wcoredump, posix-idris"
coredump : CInt -> Bits8

%foreign "C:li_wifstopped, posix-idris"
stopped : CInt -> Bits8

%foreign "C:li_wstopsig, posix-idris"
stopsig : CInt -> Bits32

%foreign "C:li_wifcontinued, posix-idris"
continued : CInt -> Bits8

public export
data ProcStatus : Type where
  Exited    : Bits8 -> ProcStatus
  Signaled  : Signal -> (coreDumped : Bool) -> ProcStatus
  Stopped   : Signal -> ProcStatus
  Continued : ProcStatus
  Other     : CInt -> ProcStatus

%runElab derive "ProcStatus" [Show,Eq]

export
procStatus : CInt -> ProcStatus
procStatus i =
  if      toBool $ exited    i then Exited (exitstatus i)
  else if toBool $ signaled  i then Signaled (S $ termsig i) (toBool $ coredump i)
  else if toBool $ stopped   i then Stopped (S $ stopsig i)
  else if toBool $ continued i then Continued
  else                              Other i
