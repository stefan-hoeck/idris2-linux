module Example.Util.File

import Data.Vect
import Data.Maybe0
import Data.Array.Index
import Data.Buffer.Core
import Data.C.Ptr

import public Example.Util.Prog
import public System.Posix.File

%default total

tryLT : (m,n : Nat) -> Maybe0 (LT m n)
tryLT m n with (m < n) proof eq
  _ | True  = Just0 (ltOpReflectsLT m n eq)
  _ | False = Nothing0

parameters {auto has : Has Errno es}

  export %inline
  withFile : String -> Flags -> Mode -> (Fd -> Prog es a) -> Prog es a
  withFile pth fs m = use1 (openFile pth fs m)

  export
  readFile : (0 r : Type) -> FromBuf r => String -> Bits32 -> Prog es r
  readFile r pth buf = withFile pth O_RDONLY 0 $ \fd => read fd r buf

  export covering
  stream :
       {auto fid : FileDesc a}
    -> (0 r : Type)
    -> {auto frb : FromBuf r}
    -> (fd : a)
    -> (buffer : Bits32)
    -> (r -> Prog es ())
    -> Prog es Bool
  stream r fd buf run =
    readres fd r buf >>= \case
      EOI         => pure True
      Closed      => pure False
      NoData      => stream r fd buf run
      Interrupted => stream r fd buf run
      Res v       => run v >> stream r fd buf run

  export
  readVect :
       {0 fd   : Type}
    -> {auto _ : SizeOf a}
    -> {auto _ : Deref a}
    -> {auto _ : FileDesc fd}
    -> fd
    -> (n      : Nat)
    -> Prog es (Vect n a)
  readVect fd n =
    use1 (cptrOf a n) $ \p => do
      vs <- readPtr fd (List a) p
      case toVect n vs of
        Just r => pure r
        Nothing => throw EINVAL

  export
  readVal :
       {0 fd   : Type}
    -> {auto _ : SizeOf a}
    -> {auto _ : Deref a}
    -> {auto _ : FileDesc fd}
    -> fd
    -> Prog es a
  readVal fd = head <$> readVect fd 1

  export covering
  streamPtr :
       {auto fid : FileDesc a}
    -> (0 r      : Type)
    -> {auto frb : FromPtr r}
    -> (fd  : a)
    -> CPtr
    -> (r -> Prog es ())
    -> Prog es Bool
  streamPtr r fd cp run =
    readPtrRes fd r cp >>= \case
      Interrupted => streamPtr r fd cp run
      NoData      => streamPtr r fd cp run
      Closed      => pure False
      EOI         => pure True
      Res res     => run res >> streamPtr r fd cp run
