module System.Posix.Process.ProcStatus

import public Data.C.Ptr
import System.Posix.Errno
import System.Posix.Signal

%default total

%foreign "C:li_wifexited, posix-idris"
prim__exited : CInt -> Bits8

%foreign "C:li_wexitstatus, posix-idris"
prim__exitstatus : CInt -> Bits8

%foreign "C:li_wifsignaled, posix-idris"
prim__signaled : CInt -> Bits8

%foreign "C:li_wtermsig, posix-idris"
prim__termsig : CInt -> Bits32

%foreign "C:li_wcoredump, posix-idris"
prim__coredump : CInt -> Bits8

%foreign "C:li_wifstopped, posix-idris"
prim__stopped : CInt -> Bits8

%foreign "C:li_wstopsig, posix-idris"
prim__stopsig : CInt -> Bits32

%foreign "C:li_wifcontinued, posix-idris"
prim__continued : CInt -> Bits8

||| Process status returned by a call to `wait` or `waitpid`.
public export
record ProcStatus where
  constructor PS
  status : CInt

public export %inline
SizeOf ProcStatus where
  sizeof_ = sizeof CInt

export %inline
Deref ProcStatus where
  deref = map PS . deref

export %inline
SetPtr ProcStatus where
  setPtr p = setPtr p . status

||| `True` if the process exited normally.
export %inline
exited : ProcStatus -> Bool
exited s = toBool $ prim__exited s.status

||| Returns the exit status with which the process exited.
export %inline
exitstatus : ProcStatus -> Bits8
exitstatus s = prim__exitstatus s.status

||| `True` if the process has been killed by a signal.
export %inline
signaled : ProcStatus -> Bool
signaled s = toBool $ prim__signaled s.status

||| Returns the signal the process was killed with.
export %inline
termsig : ProcStatus -> Signal
termsig s = S $ prim__termsig s.status

||| `True` if the process has dumped core.
export %inline
coredump : ProcStatus -> Bool
coredump s = toBool $ prim__coredump s.status

||| `True` if the process has been stopped by a signal.
export %inline
stopped : ProcStatus -> Bool
stopped s = toBool $ prim__stopped s.status

||| Returns the signal the process was stopped with.
export %inline
stopsig : ProcStatus -> Signal
stopsig s = S $ prim__stopsig s.status

||| `True` if the process has been awakend with `SIGCONT`.
export %inline
continued : ProcStatus -> Bool
continued s = toBool $ prim__continued s.status
