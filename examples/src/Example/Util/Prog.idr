module Example.Util.Prog

import public Control.Monad.Either
import public Data.List.Quantifiers.Extra
import System.Linux.File

%default total

||| An example program that can fail with one of the listed errors and
||| produces a result of the given type.
public export
0 Prog : List Type -> Type -> Type
Prog es a = EitherT (HSum es) IO a

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

||| Inject an effectful computation of type `Either e a` into a `Prog es a`.
export
injectIO : Has e es => IO (Either e a) -> Prog es a
injectIO io = liftIO io >>= injectEither

||| A specialized version of `injectIO` with better type inference
export %inline
wrapIO : IO (Either e a) -> Prog [e] a
wrapIO = injectIO

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

||| Specialized version of `handleErrors` for better type inference
export %inline
handleError : Handler e -> Prog [e] () -> Prog fs ()
handleError h = handleErrors [h]

export
logAndDropErr : Has e es => (e -> Prog [] a) -> Prog es a -> Prog es a
logAndDropErr h =
  bracketCase $ \case
    Right v => pure v
    Left  x => maybe (throwError x) (anyErr . h) (project e x)

--------------------------------------------------------------------------------
-- Running programs
--------------------------------------------------------------------------------

||| Runs a program that has all its errors handled.
export
runProg : Prog [] a -> IO a
runProg p = runEitherT p >>= \(Right v) => pure v

export %inline
runProgWith : All Handler es -> Prog es () -> IO ()
runProgWith hs = runProg . handleErrors hs

export %inline
prettyOut : Interpolation a => a -> Prog [] ()
prettyOut = putStrLn . interpolate

export %inline
prettyErr : Interpolation a => a -> Prog [] ()
prettyErr = ignore . liftIO . writeStrLn Stderr . interpolate
