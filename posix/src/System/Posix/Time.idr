module System.Posix.Time

import Data.C.Ptr

import Derive.Prelude

import System.Posix.File.ReadRes
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
  record STimespec (s : Type) where
    constructor TS
    ptr : AnyPtr

  export %inline
  Struct STimespec where
    swrap   = TS
    sunwrap = ptr

  public export %inline
  SizeOf (STimespec s) where
    sizeof_ = timespec_size

  public export
  0 IOTimespec : Type
  IOTimespec = STimespec World

  ||| Reads the `tv_sec` field of a `timespec` pointer.
  export %inline
  sec : STimespec s -> F1 s TimeT
  sec (TS p) = ffi (prim__get_tv_sec p)

  ||| Reads the `tv_nsec` field of a `timespec` pointer.
  export %inline
  nsec : STimespec s -> F1 s NsecT
  nsec (TS p) = ffi (prim__get_tv_nsec p)

  ||| Sets the `tv_sec` field of a `timespec` pointer.
  export %inline
  setSec : STimespec s -> TimeT -> F1 s ()
  setSec (TS p) t = ffi (prim__set_tv_sec p t)

  ||| Sets the `tv_nsec` field of a `timespec` pointer.
  export %inline
  setNsec : STimespec s -> NsecT -> F1 s ()
  setNsec (TS p) t = ffi (prim__set_tv_nsec p t)

  ||| Convert a `STimespec` to a `Clock t`
  export %inline
  toClock : {t : _} -> STimespec s -> F1 s (Clock t)
  toClock ts t =
    let x0 # t := sec ts t
        x1 # t := nsec ts t
     in MkClock (cast x0) (cast x1) # t

  export
  withTimespec : Clock t -> (IOTimespec -> EPrim a) -> EPrim a
  withTimespec cl f =
    withStruct STimespec $ \ts,t =>
      let _ # t := setSec ts (cast $ seconds cl) t
          _ # t := setNsec ts (cast $ nanoseconds cl) t
       in f ts t

export %inline %hint
convertClock : {t : _} -> Convert (Clock t)
convertClock = convStruct STimespec toClock

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
  record STimeval (s : Type) where
    constructor STV
    ptr : AnyPtr

  export %inline
  Struct STimeval where
    swrap   = STV
    sunwrap = ptr

  export %inline
  SizeOf (STimeval s) where
    sizeof_ = timeval_size

  public export
  0 IOTimeval : Type
  IOTimeval = STimeval World

  export %inline
  sec : STimeval s -> F1 s TimeT
  sec s = ffi $ get_timeval_tv_sec s.ptr

  export %inline
  usec : STimeval s -> F1 s SusecondsT
  usec s = ffi $ get_timeval_tv_usec s.ptr

  export %inline
  setsec : STimeval s -> TimeT -> F1 s ()
  setsec s v = ffi $ set_timeval_tv_sec s.ptr v

  export %inline
  setusec : STimeval s -> SusecondsT -> F1 s ()
  setusec s v = ffi $ set_timeval_tv_usec s.ptr v

  ||| Pure alternative to the `STimeval` struct.
  public export
  record Timeval where
    constructor TV
    sec  : TimeT
    usec : SusecondsT

  %runElab derive "Timeval" [Show,Eq]

  export %inline
  stimeval : Timeval -> F1 s (STimeval s)
  stimeval (TV s u) t = let p # t := ffi (prim__timeval s u) t in STV p # t

  export
  timeval : STimeval s -> F1 s Timeval
  timeval stv t =
    let sec  # t := STimeval.sec stv t
        usec # t := STimeval.usec stv t
     in TV sec usec # t

export %inline %hint
convertTimeval : Convert Timeval
convertTimeval = convStruct STimeval timeval

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
  record Itimerval (s : Type) where
    constructor ITV
    ptr : AnyPtr

  export %inline
  Struct Itimerval where
    swrap   = ITV
    sunwrap = ptr

  export %inline
  SizeOf (Itimerval s) where
    sizeof_ = itimerval_size

  public export
  0 IOTimerval : Type
  IOTimerval = Itimerval World

  export %inline
  interval : Itimerval s -> F1 s (STimeval s)
  interval s t = mapR1 STV $ ffi (get_itimerval_it_interval s.ptr) t

  export %inline
  value : Itimerval s -> F1 s (STimeval s)
  value s t = mapR1 STV $ ffi (get_itimerval_it_value s.ptr) t

  export %inline
  setinterval : Itimerval s -> STimeval s -> F1 s ()
  setinterval s v = ffi $ set_itimerval_it_interval s.ptr v.ptr

  export %inline
  setvalue : Itimerval s -> STimeval s -> F1 s ()
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
  itimerval : Timerval -> F1 s (Itimerval s)
  itimerval (TRV (TV si ui) (TV sv uv)) t =
    mapR1 ITV $ ffi (prim__itimerval si ui sv uv) t

  export
  timerval : Itimerval s -> F1 s Timerval
  timerval itv t =
    let siv  # t := Itimerval.interval itv t
        iv   # t := timeval siv t
        sval # t := Itimerval.value itv t
        val  # t := timeval sval t
     in TRV iv val # t

export %inline %hint
convertTimerval : Convert Timerval
convertTimerval = convStruct Itimerval timerval

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
  record Itimerspec (s : Type) where
    constructor ITS
    ptr : AnyPtr

  export %inline
  Struct Itimerspec where
    swrap   = ITS
    sunwrap = ptr

  export %inline
  SizeOf (Itimerspec s) where
    sizeof_ = itimerspec_size

  public export
  0 IOTimerspec : Type
  IOTimerspec = Itimerspec World

  namespace Itimerspec
    export %inline
    interval : Itimerspec s -> F1 s (STimespec s)
    interval s t = mapR1 wrap $ ffi (get_itimerspec_it_interval s.ptr) t

    export %inline
    value : Itimerspec s -> F1 s (STimespec s)
    value s t = mapR1 wrap $ ffi (get_itimerspec_it_value s.ptr) t

    export %inline
    setinterval : Itimerspec s -> STimespec s -> F1 s ()
    setinterval s v = ffi $ set_itimerspec_it_interval s.ptr (unwrap v)

    export %inline
    setvalue : Itimerspec s -> STimespec s -> F1 s ()
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
    -> F1 s (Itimerspec s)
  itimerspec si ni sv nv t =
    mapR1 ITS $ ffi (prim__itimerspec si ni sv nv) t

  ||| Pure alternative to the `Itimerspec` struct.
  public export
  record Timerspec where
    constructor TS
    interval : Clock Duration
    value    : Clock Duration

  %runElab derive "Timerspec" [Show,Eq]

  export
  timerspec : Itimerspec s -> F1 s Timerspec
  timerspec its t =
    let siv  # t := Itimerspec.interval its t
        iv   # t := toClock siv t
        sval # t := Itimerspec.value its t
        val  # t := toClock sval t
     in TS iv val # t

  export
  duration : TimeT -> NsecT -> Clock Duration
  duration s ns = makeDuration (cast s) (cast ns)

export %inline %hint
convTimerspec : Convert Timerspec
convTimerspec = convStruct Itimerspec timerspec
