module Example.Util.Signal

import Derive.Finite
import Derive.Prelude
import public Example.Util.Prog
import public System.Posix.Signal

%default total
%language ElabReflection

export %inline
Ord Signal where
  compare = compare `on` signalCode

%runElab derive "PosixSignal" [Show,Finite]
%runElab derive "Signal" [Show,Finite]

export
filterM : Monad f => (a -> f Bool) -> List a -> f (List a)
filterM f [] = pure []
filterM f (h::t) =
  f h >>= \case
    True  => (h::) <$> filterM f t
    False => filterM f t

export
Interpolation PosixSignal where
  interpolate = toUpper . show

export
Interpolation Signal where
  interpolate (SigPosix x) = interpolate x
  interpolate v            = toUpper $ show v

export
withSigset : (full : Bool) -> (SigsetT -> Prog es a) -> Prog es a
withSigset b f = do
  s <- if b then fullSigset else emptySigset
  finally (freeSigset s) (f s)

export
pendingSignals : Has Errno es => Prog es (List Signal)
pendingSignals = do
  s  <- sigpending
  ss <- filterM (sigismember s) values
  freeSigset s
  pure ss

