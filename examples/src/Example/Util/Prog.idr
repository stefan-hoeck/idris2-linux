module Example.Util.Prog

import public Control.Monad.Either
import public Data.List.Quantifiers.Extra
import System.Posix.File
import Data.C.Ptr

%default total

||| An example program that can fail with one of the listed errors and
||| produces a result of the given type.
public export
0 Prog : List Type -> Type -> Type
Prog es a = EitherT (HSum es) IO a

export %inline
Has Errno es => ErrIO (EitherT (HSum es) IO) where
  eprim act =
    MkEitherT $ runIO $ \t => case act t of
      R r t => Right r # t
      E x t => Left (inject x) # t

--------------------------------------------------------------------------------
-- Lifting computations
--------------------------------------------------------------------------------

||| Fails with the given exception
export %inline
fail : Has e es => e -> Prog es a
fail v = throwError (inject v)

||| Injects an `Either e a` into a `Prog es a` where `e` must be an element
||| of `es`.
export
injectEither : Has e es => Either e a -> Prog es a
injectEither (Left x)  = fail x
injectEither (Right x) = pure x

--------------------------------------------------------------------------------
-- Error handling
--------------------------------------------------------------------------------

||| An error handler for errors of type `a`
public export
0 Handler : Type -> Type
Handler a = a -> Prog [] ()

||| Generalized continuation: Bind and error handling
export
bracketCase : (Either (HSum es) a -> Prog fs b) -> Prog es a -> Prog fs b
bracketCase f prog = MkEitherT $ runEitherT prog >>= runEitherT . f

||| A prog that cannot fail can always be converted to a prog that
||| could potentially fail.
export
anyErr : Prog [] a -> Prog es a
anyErr = bracketCase $ \(Right v) => pure v

||| Forget all errors and the result and run a prog only for its effects
export
clear : Prog es a -> Prog [] ()
clear = bracketCase (const $ pure ())

||| Guaranteed to run a cleanup function based on a program's outcome
export
guaranteeCase : (Either (HSum es) a -> Prog [] ()) -> Prog es a -> Prog es a
guaranteeCase f = bracketCase $ \x => anyErr (f x) >> liftEither x

||| Guaranteed to run a cleanup function independent of a program's outcome
export
finally : Prog [] () -> Prog es a -> Prog es a
finally = guaranteeCase . const

||| Handles all errors of a program.
export
handleErrors : (hs : All Handler es) -> Prog es () -> Prog fs ()
handleErrors hs =
  bracketCase $ \case
    Left x  => anyErr $ collapse' $ hzipWith id hs x
    Right _ => pure ()

export
onErrno : Has Errno es => Errno -> Prog es a -> Prog es a -> Prog es a
onErrno err h =
  bracketCase $ \case
    Right a => pure a
    Left  x => case project Errno x of
      Just e  => if err == e then h else fail e
      Nothing => throwError x

||| Specialized version of `handleErrors` for better type inference
export %inline
handleError : Handler e -> Prog [e] () -> Prog fs ()
handleError h = handleErrors [h]

export
dropErr : Has e es => (e -> a) -> Prog es a -> Prog es a
dropErr f =
  bracketCase $ \case
    Right v => pure v
    Left  x => maybe (throwError x) (pure . f) (project e x)

export
logAndDropErr : Has e es => (e -> Prog [] a) -> Prog es a -> Prog es a
logAndDropErr h =
  bracketCase $ \case
    Right v => pure v
    Left  x => maybe (throwError x) (anyErr . h) (project e x)

--------------------------------------------------------------------------------
-- Running programs
--------------------------------------------------------------------------------

export %inline
stdoutLn' : String -> Prog [] ()
stdoutLn' = clear {es = [Errno]} . stdoutLn

export %inline
stderrLn' : String -> Prog [] ()
stderrLn' = clear {es = [Errno]} . stderrLn

||| Runs a program that has all its errors handled.
export
runProg : Prog [] a -> IO a
runProg p = runEitherT p >>= \(Right v) => pure v

export %inline
runProgWith : All Handler es -> Prog es () -> IO ()
runProgWith hs = runProg . handleErrors hs

export %inline
prettyOut : Interpolation a => a -> Prog [] ()
prettyOut = stdoutLn' . interpolate

export %inline
prettyErr : Interpolation a => a -> Prog [] ()
prettyErr = stderrLn' . interpolate

export %inline
prettyErrno : Errno -> Prog [] ()
prettyErrno = prettyErr

--------------------------------------------------------------------------------
-- Resource handling
--------------------------------------------------------------------------------

public export
interface Resource a where
  cleanup : a -> Prog [] ()

||| Allocate a resource, use it in a program, and make sure to release it
||| afterwards.
export %inline
use1 : Resource a => Prog es a -> (a -> Prog es b) -> Prog es b
use1 alloc run = alloc >>= \r => finally (cleanup r) (run r)

||| Like `use1` but for a heterogeneous list of resources.
export %inline
use : All Resource ts => All (Prog es) ts -> (HList ts -> Prog es b) -> Prog es b
use @{[]}   []     run = run []
use @{_::_} (h::t) run = use1 h (\r => use t (run . (r::)))

export %inline
Resource (CArrayIO n a) where cleanup = liftIO . free

export %inline
Resource CPtr where cleanup = freePtr

export %inline
Struct a => Resource a where cleanup = freeStruct
