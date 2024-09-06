module Example.Util.Signal

import Derive.Finite
import Derive.Prelude
import public Example.Util.Prog
import public System.Posix.Signal

%default total
%language ElabReflection

export
Finite Signal where
  values =
    map Signal.Types.S $
      [1..8] ++ [10..15] ++ [17..27] ++ [29,31] ++ [sig SIGRTMIN .. sig SIGRTMAX]

export
Interpolation Signal where interpolate = show . sig

export
filterM : Monad f => (a -> f Bool) -> List a -> f (List a)
filterM f [] = pure []
filterM f (h::t) =
  f h >>= \case
    True  => (h::) <$> filterM f t
    False => filterM f t

export
withSigset : (full : Bool) -> (SigsetT -> Prog es a) -> Prog es a
withSigset b f = do
  s <- if b then fullSigset else emptySigset
  finally (freeSigset s) (f s)

export
withSiginfo : (SiginfoT -> Prog es a) -> Prog es a
withSiginfo f = do
  s <- allocSiginfoT
  finally (freeSiginfoT s) (f s)

export
pendingSignals : Has Errno es => Prog es (List Signal)
pendingSignals = do
  s  <- sigpending
  ss <- filterM (sigismember s) values
  freeSigset s
  pure ss

