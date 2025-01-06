module System.Posix.Time

import Data.C.Ptr

import Derive.Prelude

import public Data.C.Integer
import public System.Clock
import public System.Posix.Errno
import public System.Posix.Time.Types
import public System.Posix.Timer.Types

%default total
%language ElabReflection

export %inline
(.secs) : Clock t -> TimeT
(.secs) = cast . seconds

export %inline
(.nsecs) : Clock t -> TimeT
(.nsecs) = cast . nanoseconds

--------------------------------------------------------------------------------
-- STimespec
--------------------------------------------------------------------------------

namespace Timespec
  %foreign "C:get_tv_sec, posix-idris"
  prim__get_tv_sec: AnyPtr -> PrimIO TimeT

  %foreign "C:get_tv_nsec, posix-idris"
  prim__get_tv_nsec: AnyPtr -> PrimIO NsecT

  %foreign "C:set_tv_sec, posix-idris"
  prim__set_tv_sec: AnyPtr -> TimeT -> PrimIO ()

  %foreign "C:set_tv_nsec, posix-idris"
  prim__set_tv_nsec: AnyPtr -> NsecT -> PrimIO ()

  ||| A wrapper around a `struct timespec` pointer.
  export
  record STimespec where
    constructor TS
    ptr : AnyPtr

  export %inline
  Struct STimespec where
    wrap   = TS
    unwrap = ptr

  public export %inline
  SizeOf STimespec where
    sizeof_ = timespec_size

  export %inline
  InIO STimespec

  ||| Reads the `tv_sec` field of a `timespec` pointer.
  export %inline
  sec : (r : STimespec) -> (0 p : Res r rs) => F1 rs TimeT
  sec (TS p) = ffi (prim__get_tv_sec p)

  ||| Reads the `tv_nsec` field of a `timespec` pointer.
  export %inline
  nsec : (r : STimespec) -> (0 p : Res r rs) => F1 rs NsecT
  nsec (TS p) = ffi (prim__get_tv_nsec p)

  ||| Sets the `tv_sec` field of a `timespec` pointer.
  export %inline
  setSec : (r : STimespec) -> TimeT -> (0 p : Res r rs) => F1 rs ()
  setSec (TS p) t = ffi (prim__set_tv_sec p t)

  ||| Sets the `tv_nsec` field of a `timespec` pointer.
  export %inline
  setNsec : (r : STimespec) -> NsecT -> (0 p : Res r rs) => F1 rs ()
  setNsec (TS p) t = ffi (prim__set_tv_nsec p t)

  ||| Convert a `STimespec` to a `Clock t`
  export %inline
  toClock : {t : _} -> (r : STimespec) -> (0 p : Res r rs) => F1 rs (Clock t)
  toClock ts t =
    let x0 # t := sec ts t
        x1 # t := nsec ts t
     in MkClock (cast x0) (cast x1) # t

  export
  withTimespec : Clock t -> (STimespec -> EPrim a) -> EPrim a
  withTimespec cl f =
    withStruct STimespec $ \ts,t =>
      let _ # t := setSec ts (cast $ seconds cl) t
          _ # t := setNsec ts (cast $ nanoseconds cl) t
       in f ts t

--------------------------------------------------------------------------------
-- STimeval
--------------------------------------------------------------------------------

namespace STimeval

  %foreign "C:get_timeval_tv_sec, posix-idris"
  get_timeval_tv_sec: AnyPtr -> PrimIO TimeT

  %foreign "C:get_timeval_tv_usec, posix-idris"
  get_timeval_tv_usec: AnyPtr -> PrimIO SusecondsT

  %foreign "C:set_timeval_tv_sec, posix-idris"
  set_timeval_tv_sec: AnyPtr -> TimeT -> PrimIO ()

  %foreign "C:set_timeval_tv_usec, posix-idris"
  set_timeval_tv_usec: AnyPtr -> SusecondsT -> PrimIO ()

  %foreign "C:li_timeval, posix-idris"
  prim__timeval : TimeT -> SusecondsT -> PrimIO AnyPtr

  export
  record STimeval where
    constructor STV
    ptr : AnyPtr

  export %inline
  Struct STimeval where
    wrap   = STV
    unwrap = ptr

  export %inline
  SizeOf STimeval where
    sizeof_ = timeval_size

  export %inline
  InIO STimeval

  export %inline
  sec : (r : STimeval) -> (0 p : Res r rs) => F1 rs TimeT
  sec s = ffi $ get_timeval_tv_sec s.ptr

  export %inline
  usec : (r : STimeval) -> (0 p : Res r rs) => F1 rs SusecondsT
  usec s = ffi $ get_timeval_tv_usec s.ptr

  export %inline
  setsec : (r : STimeval) -> TimeT -> (0 p : Res r rs) => F1 rs ()
  setsec s v = ffi $ set_timeval_tv_sec s.ptr v

  export %inline
  setusec : (r : STimeval) -> SusecondsT -> (0 p : Res r rs) => F1 rs ()
  setusec s v = ffi $ set_timeval_tv_usec s.ptr v

  ||| Pure alternative to the `STimeval` struct.
  public export
  record Timeval where
    constructor TV
    sec  : TimeT
    usec : SusecondsT

  %runElab derive "Timeval" [Show,Eq]

  export %inline
  stimeval : Timeval -> F1 [World] STimeval
  stimeval (TV s u) = toF1 $ primMap STV $ prim__timeval s u

  export
  timeval : (r : STimeval) -> (0 p : Res r rs) => F1 rs Timeval
  timeval stv t =
    let sec  # t := STimeval.sec stv t
        usec # t := STimeval.usec stv t
     in TV sec usec # t

--------------------------------------------------------------------------------
-- Timerval
--------------------------------------------------------------------------------

namespace Itimerval
  %foreign "C:get_itimerval_it_interval, posix-idris"
  get_itimerval_it_interval: AnyPtr -> PrimIO AnyPtr

  %foreign "C:get_itimerval_it_value, posix-idris"
  get_itimerval_it_value: AnyPtr -> PrimIO AnyPtr

  %foreign "C:set_itimerval_it_interval, posix-idris"
  set_itimerval_it_interval: AnyPtr -> AnyPtr -> PrimIO ()

  %foreign "C:set_itimerval_it_value, posix-idris"
  set_itimerval_it_value: AnyPtr -> AnyPtr -> PrimIO ()

  %foreign "C:li_itimerval, posix-idris"
  prim__itimerval : TimeT -> SusecondsT -> TimeT -> SusecondsT -> PrimIO AnyPtr

  export
  record Itimerval where
    constructor ITV
    ptr : AnyPtr

  export %inline
  Struct Itimerval where
    wrap   = ITV
    unwrap = ptr

  export %inline
  SizeOf Itimerval where
    sizeof_ = itimerval_size

  export
  InIO Itimerval

  export %inline
  interval : (r : Itimerval) -> F1 [World] STimeval
  interval s = toF1 $ primMap STV $ get_itimerval_it_interval s.ptr

  export %inline
  value : (r : Itimerval) -> F1 [World] STimeval
  value s = toF1 $ primMap STV $ get_itimerval_it_value s.ptr

  export %inline
  setinterval : (r : Itimerval) -> STimeval -> F1 [World] ()
  setinterval s v = ffi $ set_itimerval_it_interval s.ptr v.ptr

  export %inline
  setvalue : (r : Itimerval) -> STimeval -> F1 [World] ()
  setvalue s v = ffi $ set_itimerval_it_value s.ptr v.ptr

  ||| Pure alternative to the `Itimerval` struct.
  public export
  record Timerval where
    constructor TRV
    interval : Timeval
    value    : Timeval

  %runElab derive "Timerval" [Show,Eq]

  ||| Creates and sets the fields of a `Itimerval` pointer.
  |||
  ||| The allocated memory must be freed via `freeStruct`.
  export %inline
  itimerval : Timerval -> F1 [World] Itimerval
  itimerval (TRV (TV si ui) (TV sv uv)) = do
    toF1 $ primMap ITV $ prim__itimerval si ui sv uv

  export
  timerval : Itimerval -> F1 [World] Timerval
  timerval itv t =
    let siv  # t := Itimerval.interval itv t
        iv   # t := timeval siv t
        sval # t := Itimerval.value itv t
        val  # t := timeval sval t
     in TRV iv val # t

--------------------------------------------------------------------------------
-- Timerspec
--------------------------------------------------------------------------------

namespace Itimerspec
  export %foreign "C:get_itimerspec_it_interval, posix-idris"
  get_itimerspec_it_interval: AnyPtr -> PrimIO AnyPtr

  export %foreign "C:get_itimerspec_it_value, posix-idris"
  get_itimerspec_it_value: AnyPtr -> PrimIO AnyPtr

  export %foreign "C:set_itimerspec_it_interval, posix-idris"
  set_itimerspec_it_interval: AnyPtr -> AnyPtr -> PrimIO ()

  export %foreign "C:set_itimerspec_it_value, posix-idris"
  set_itimerspec_it_value: AnyPtr -> AnyPtr -> PrimIO ()

  %foreign "C:li_itimerspec, posix-idris"
  prim__itimerspec : TimeT -> NsecT -> TimeT -> NsecT -> PrimIO AnyPtr

  ||| Note: Also this is POSIX compliant, it is not available on
  ||| MacOS (Darwin). Idris programs making use of this might fail on
  ||| Darwin during code generation.
  export
  record Itimerspec where
    constructor ITS
    ptr : AnyPtr

  export %inline
  Struct Itimerspec where
    wrap   = ITS
    unwrap = ptr

  export %inline
  SizeOf Itimerspec where
    sizeof_ = itimerspec_size

  namespace Itimerspec
    export %inline
    interval : Itimerspec -> F1 [World] STimespec
    interval s = toF1 $ primMap wrap $ get_itimerspec_it_interval s.ptr

    export %inline
    value : Itimerspec -> F1 [World] STimespec
    value s = toF1 $ primMap wrap $ get_itimerspec_it_value s.ptr

    export %inline
    setinterval : Itimerspec -> STimespec -> F1 [World] ()
    setinterval s v = ffi $ set_itimerspec_it_interval s.ptr (unwrap v)

    export %inline
    setvalue : Itimerspec -> STimespec -> F1 [World] ()
    setvalue s v = ffi $ set_itimerspec_it_value s.ptr (unwrap v)

  ||| Creates and sets the fields of a `Itimerspec` pointer.
  |||
  ||| The allocated memory must be freed via `freeStruct`.
  export %inline
  itimerspec :
       (secInterval  : TimeT)
    -> (usecInterval : NsecT)
    -> (secValue     : TimeT)
    -> (usecValue    : NsecT)
    -> F1 [World] Itimerspec
  itimerspec si ni sv nv = do
    toF1 $ primMap ITS $ prim__itimerspec si ni sv nv

  ||| Pure alternative to the `Itimerspec` struct.
  public export
  record Timerspec where
    constructor TS
    interval : Clock Duration
    value    : Clock Duration

  %runElab derive "Timerspec" [Show,Eq]

  export
  timerspec : Itimerspec -> F1 [World] Timerspec
  timerspec its t =
    let siv  # t := Itimerspec.interval its t
        iv   # t := toClock siv t
        sval # t := Itimerspec.value its t
        val  # t := toClock sval t
     in TS iv val # t

  export
  duration : TimeT -> NsecT -> Clock Duration
  duration s ns = makeDuration (cast s) (cast ns)
