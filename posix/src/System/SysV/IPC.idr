module System.SysV.IPC

import public Data.C.Ptr
import public System.Posix.Errno

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

export %foreign "C:li_ipc_private, posix-idris"
IPC_PRIVATE : KeyT

||| Flag indicating that `msgget` should fail with `EEXIST` if a queue
||| with the given key exists already.
export %foreign "C:li_ipc_excl, posix-idris"
IPC_EXCL : ModeT

||| Flag indicating that a new message queue should be created for a
||| key if it does not exist already.
export %foreign "C:li_ipc_creat, posix-idris"
IPC_CREAT : ModeT

%foreign "C:li_ftok, posix-idris"
prim__ftok : String -> Bits8 -> PrimIO CInt

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Generates a System V key based on data from an existing file (given
||| as its path) and project identifier.
export %inline
ftok : ErrIO io => String -> Bits8 -> io KeyT
ftok pth id = toVal cast $ prim__ftok pth id
