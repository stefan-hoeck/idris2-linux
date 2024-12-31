module Example.Util.Signal

import Derive.Finite
import Derive.Prelude
import public Example.Util.File
import public System.Posix.Signal

%default total

export
Interpolation Signal where interpolate = show . sig
