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

||| An interface for dealing with system errors in `IO`
public export
interface HasIO io => ErrIO io where
  error : Errno -> io a

||| Wraps a `PrimIO` with the potential of failure in an `IO` type with
||| error handling.
export %inline
errIO : ErrIO io => PrimIO (Either Errno a) -> io a
errIO run =
  primIO run >>= \case
    Left err => error err
    Right v  => pure v

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
toSize : PrimIO SsizeT -> PrimIO (Either Errno Bits32)
toSize = primMap (\r => if r < 0 then Left (fromNeg r) else Right (cast r))

export %inline
toUnit : PrimIO CInt -> PrimIO (Either Errno ())
toUnit = primMap (\r => if r < 0 then Left (fromNeg r) else Right ())

export %inline
toPidT : PrimIO PidT -> PrimIO (Either Errno PidT)
toPidT = primMap (\r => if r < 0 then Left (fromNeg r) else Right r)

export %inline
posToUnit : PrimIO Bits32 -> PrimIO (Either Errno ())
posToUnit =
  primMap $ \case
    0 => Right ()
    x => Left (EN x)

export %inline
toRes : PrimIO a -> PrimIO CInt -> PrimIO (Either Errno a)
toRes wrap act w =
  let MkIORes (Right _) w := toUnit act w
        | MkIORes (Left err) w => MkIORes (Left err) w
   in primMap Right wrap w

export %inline
toVal : (CInt -> a) -> PrimIO CInt -> PrimIO (Either Errno a)
toVal f = primMap (\r => if r < 0 then Left (fromNeg r) else Right (f r))

--------------------------------------------------------------------------------
-- General PrimIO Utilities
--------------------------------------------------------------------------------

export %inline
primStruct : (0 a : Type) -> Struct a => SizeOf a => PrimIO a
primStruct a = toPrim (allocStruct a)

export %inline
freeingStruct : Struct a => a -> b -> PrimIO b
freeingStruct v vb w =
  let MkIORes _ w := toPrim (freeStruct v) w
   in MkIORes vb w

export %inline
withStruct : (0 a : Type) -> Struct a => SizeOf a => (a -> PrimIO b) -> PrimIO b
withStruct a f w =
  let MkIORes str w := primStruct a w
      MkIORes res w := f str w
   in freeingStruct str res w

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
notErr : Errno -> PrimIO (Either Errno ()) -> PrimIO (Either Errno Bool)
notErr err f w =
  let MkIORes r w := f w
   in case r of
        Right () => MkIORes (Right True) w
        Left x   =>
          if x == err
             then MkIORes (Right False) w
             else MkIORes (Left x) w
