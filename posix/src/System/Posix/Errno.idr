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
  R : (v : t)   -> (1 w : T1 [World]) -> ERes t
  E : (x : Errno) -> (1 w : T1 [World]) -> ERes t

public export
0 EPrim : Type -> Type
EPrim t = (1 w : T1 [World]) -> ERes t

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
toVal f act t =
  let r # t := toF1 act t
   in if r < 0 then E (fromNeg r) t else R (f r) t

export %inline
toSize : PrimIO SsizeT -> EPrim Bits32
toSize act t =
  let r # t := toF1 act t
   in if r < 0 then E (fromNeg r) t else R (cast r) t

export %inline
toUnit : PrimIO CInt -> EPrim ()
toUnit act t =
  let r # t := toF1 act t
   in if r < 0 then E (fromNeg r) t else R () t

export %inline
toPidT : PrimIO PidT -> EPrim PidT
toPidT act t =
  let r # t := toF1 act t
   in if r < 0 then E (fromNeg r) t else R r t

export %inline
posToUnit : PrimIO Bits32 -> EPrim ()
posToUnit act t =
  case toF1 act t of
    0 # t => R () t
    x # t => E (EN x) t

export %inline
toRes : PrimIO a -> PrimIO CInt -> EPrim a
toRes wrap act t =
  let R _ t := toUnit act t | E x t => E x t
      r # t := toF1 wrap t
   in R r t

export %inline
ignore : EPrim a -> PrimIO ()
ignore act =
  primRun $ \t => case act t of
    R _ t => () # t
    E _ t => () # t

--------------------------------------------------------------------------------
-- General PrimIO Utilities
--------------------------------------------------------------------------------

export %inline
freeFail : Struct a => a -> Errno -> EPrim b
freeFail s err t =
  let _ # t := toF1 (prim__free $ unwrap s) t
   in E err t

export %inline
finally : PrimIO () -> EPrim a -> EPrim a
finally cleanup act t =
  case act t of
    R r t => let _ # t := toF1 cleanup t in R r t
    E x t => let _ # t := toF1 cleanup t in E x t

export %inline
primStruct : (0 a : Type) -> Struct a => SizeOf a => F1 [World] a
primStruct a = ioToF1 (allocStruct a)

export %inline
withStruct : (0 a : Type) -> Struct a => SizeOf a => (a -> EPrim b) -> EPrim b
withStruct a f t =
  let str # t := primStruct a t
   in finally (prim__free (unwrap str)) (f str) t

export %inline
withBox : (0 a : Type) -> SizeOf a => Deref a => (IOBox a -> EPrim b) -> EPrim b
withBox a f t =
  let box # t := ioToF1 (malloc a 1) t
   in finally (toPrim $ free box) (f box) t

export %inline
withPtr :  Bits32 -> (AnyPtr -> EPrim b) -> EPrim b
withPtr sz f t =
  let ptr         := prim__malloc sz
   in finally (prim__free ptr) (f ptr) t

export
primTraverse_ : (a -> PrimIO ()) -> List a -> PrimIO ()
primTraverse_ f []        w = MkIORes () w
primTraverse_ f (x :: xs) w =
  let MkIORes _ w := f x w
   in primTraverse_ f xs w

export
filterM : SnocList a -> (a -> F1 rs Bool) -> List a -> F1 rs (List a)
filterM sa f []      t = (sa <>> []) # t
filterM sa f (v::vs) t =
  let True # t := f v t | _ # t => filterM sa f vs t
   in filterM (sa :< v) f vs t

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
  -> (b -> F1 [World] c)
  -> (k : Nat)
  -> {auto 0 prf : LTE k n}
  -> F1 [World] (List c)
values cs arr f 0     t = cs # t
values cs arr f (S k) t =
  let vb # t := getNat arr k t
      vc # t := f vb t
   in values (vc::cs) arr f k t
