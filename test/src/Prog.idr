module Prog

import public Control.Monad.Either
import public Data.List.Quantifiers.Extra

%default total

public export
0 Prog : List Type -> Type -> Type
Prog es a = EitherT (HSum es) IO a

export
bracketCase : (Either (HSum es) a -> Prog fs b) -> Prog es a -> Prog fs b
bracketCase f prog = MkEitherT $ runEitherT prog >>= runEitherT . f

export
anyErr : Prog [] a -> Prog es a
anyErr =
  bracketCase $ \case
    Left _ impossible
    Right v => pure v

export
guaranteeCase : (Either (HSum es) a -> Prog [] ()) -> Prog es a -> Prog es a
guaranteeCase f = bracketCase $ \x => anyErr (f x) >> liftEither x

export
clear : Prog es a -> Prog [] ()
clear = bracketCase (const $ pure ())

export
finally : Prog [] () -> Prog es a -> Prog es a
finally = guaranteeCase . const

export %inline
fail : Has e es => e -> Prog es a
fail v = throwError (inject v)

export
injectIO : Has e es => IO (Either e a) -> Prog es a
injectIO io =
  liftIO io >>= \case
    Left x  => fail x
    Right v => pure v

export %inline
wrapIO : IO (Either e a) -> Prog [e] a
wrapIO = injectIO

public export
0 Handler : Type -> Type
Handler a = a -> Prog [] ()

export
handleErrors : (hs : All Handler es) -> Prog es () -> Prog fs ()
handleErrors hs =
  bracketCase $ \case
    Left x  => anyErr $ collapse' $ hzipWith id hs x
    Right _ => pure ()

export %inline
handleError : Handler e -> Prog [e] () -> Prog fs ()
handleError h = handleErrors [h]

export
runProg : Prog [] a -> IO a
runProg p =
  runEitherT p >>= \case
    Right v => pure v
    Left _ impossible

export %inline
prettyOut : Interpolation a => a -> Prog [] ()
prettyOut = putStrLn . interpolate
