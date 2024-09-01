module System.Linux.Time

import Data.C.Integer
import Data.C.Struct
import Derive.Prelude
import public System.Clock

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

export
toClock : {t : _} -> Timespec -> Clock t
toClock s =
  MkClock
    (cast {from = TimeT} $ getField s "tv_sec")
    (cast {from = NsecT} $ getField s "tv_nsec")
