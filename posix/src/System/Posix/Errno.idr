module System.Posix.Errno

import Data.C.Integer
import Data.C.Ptr
import Data.Finite
import Data.Maybe
import Data.SortedMap
import public System.Posix.Errno.Type

--------------------------------------------------------------------------------
-- Interface
--------------------------------------------------------------------------------

public export
data ERes : Type -> Type where
  R : (v : t)   -> (1 w : %World) -> ERes t
  E : (x : Errno) -> (1 w : %World) -> ERes t

public export
0 EPrim : Type -> Type
EPrim t = (1 w : %World) -> ERes t

||| An interface for dealing with system errors in `IO`
public export
interface HasIO io => ErrIO io where
  eprim : EPrim a -> io a

||| Prints the error text and name of a system error.
export %inline
Interpolation Errno where
  interpolate x = "\{errorText x} (\{errorName x})"

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

||| Converts 0 to `False`, everything else to `True`
public export %inline
toBool : Bits8 -> Bool
toBool 0 = False
toBool _ = True

||| Converts a negative number to a system error.
export %inline
fromNeg : Neg n => Cast n Bits32 => n -> Errno
fromNeg = EN . cast . negate

export %inline
primMap : (a -> b) -> PrimIO a -> PrimIO b
primMap f act w =
  let MkIORes v w := act w
   in MkIORes (f v) w

export %inline
eprimMap : (a -> b) -> EPrim a -> EPrim b
eprimMap f act w =
  let R v w := act w | E x w => E x w
   in R (f v) w

export %inline
toVal : (CInt -> a) -> PrimIO CInt -> EPrim a
toVal f act w =
  let MkIORes r w := act w
   in if r < 0 then E (fromNeg r) w else R (f r) w

export %inline
toSize : PrimIO SsizeT -> EPrim Bits32
toSize act w =
  let MkIORes r w := act w
   in if r < 0 then E (fromNeg r) w else R (cast r) w

export %inline
toUnit : PrimIO CInt -> EPrim ()
toUnit act w =
  let MkIORes r w := act w
   in if r < 0 then E (fromNeg r) w else R () w

export %inline
toPidT : PrimIO PidT -> EPrim PidT
toPidT act w =
  let MkIORes r w := act w
   in if r < 0 then E (fromNeg r) w else R r w

export %inline
posToUnit : PrimIO Bits32 -> EPrim ()
posToUnit act w =
  let MkIORes 0 w := act w | MkIORes x w => E (EN x) w
   in R () w

export %inline
toRes : PrimIO a -> PrimIO CInt -> EPrim a
toRes wrap act w =
  let R _ w       := toUnit act w | E x w => E x w
      MkIORes r w := wrap w
   in R r w

export %inline
ignore : EPrim a -> PrimIO ()
ignore act w =
  case act w of
    R _ w => MkIORes () w
    E _ w => MkIORes () w

--------------------------------------------------------------------------------
-- General PrimIO Utilities
--------------------------------------------------------------------------------

export %inline
primStruct : (0 a : Type) -> Struct a => SizeOf a => PrimIO a
primStruct a = toPrim (allocStruct a)

export %inline
freeFail : Struct a => a -> Errno -> EPrim b
freeFail v x w =
  let MkIORes _ w := prim__free (unwrap v) w
   in E x w

export %inline
freeSucc : Struct a => a -> b -> EPrim b
freeSucc str v w =
  let MkIORes _ w := prim__free (unwrap str) w
   in R v w

export %inline
withStruct : (0 a : Type) -> Struct a => SizeOf a => (a -> EPrim b) -> EPrim b
withStruct a f w =
  let MkIORes str w := primStruct a w
      R v w := f str w | E x w => freeFail str x w
   in freeSucc str v w

export %inline
withBox : (0 a : Type) -> SizeOf a => Deref a => (IOBox a -> EPrim b) -> EPrim b
withBox a f w =
  let MkIORes box w := toPrim (malloc a 1) w
      R r w := f box w | E x w => let MkIORes _ w := toPrim (free box) w in E x w
      MkIORes _   w := toPrim (free box) w
   in R r w

export %inline
withPtr :  Bits32 -> (AnyPtr -> EPrim b) -> EPrim b
withPtr sz f w =
  let ptr         := prim__malloc sz
      R v w       := f ptr w
        | E x w =>
            let MkIORes _ w := prim__free ptr w
             in E x w
      MkIORes _ w := prim__free ptr w
   in R v w

export
primTraverse_ : (a -> PrimIO ()) -> List a -> PrimIO ()
primTraverse_ f []        w = MkIORes () w
primTraverse_ f (x :: xs) w =
  let MkIORes _ w := f x w
   in primTraverse_ f xs w

export
filterM : SnocList a -> (a -> PrimIO Bool) -> List a -> PrimIO (List a)
filterM sa f []     w = MkIORes (sa <>> []) w
filterM sa f (h::t) w =
  let MkIORes True w := f h w | MkIORes _ w => filterM sa f t w
   in filterM (sa :< h) f t w

export
notErr : Errno -> EPrim () -> EPrim Bool
notErr err f w =
  case f w of
    R () w => R True w
    E x  w => case x == err of
      True  => R False w
      False => E x w

export
values :
     {auto der : Deref b}
  -> {auto sof : SizeOf b}
  -> List c
  -> CArrayIO n b
  -> (b -> PrimIO c)
  -> (k : Nat)
  -> {auto 0 prf : LTE k n}
  -> PrimIO (List c)
values cs arr f 0     w = MkIORes cs w
values cs arr f (S k) w =
  let MkIORes vb w := primRun (getNat arr k) w
      MkIORes vc w := f vb w
   in values (vc::cs) arr f k w
