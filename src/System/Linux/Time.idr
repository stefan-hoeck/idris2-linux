module System.Linux.Time

import Data.C.Integer
import Data.C.Struct
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Structs
--------------------------------------------------------------------------------

public export
0 Timespec : Type
Timespec =
  Struct "timespec"
    [ ("tv_sec", TimeT)
    , ("tv_nsec", NsecT)
    ]

public export
record Time where
  constructor T
  seconds     : TimeT
  nanoseconds : NsecT

%runElab derive "Time" [Show,Eq,Ord]

export
toTime : Timespec -> Time
toTime s =
  T
    { seconds     = getField s "tv_sec"
    , nanoseconds = getField s "tv_nsec"
    }
