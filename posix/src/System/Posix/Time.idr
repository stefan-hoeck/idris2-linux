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

  ||| Reads the `tv_sec` field of a `timespec` pointer.
  export %inline
  sec : STimespec -> PrimIO TimeT
  sec (TS p) = prim__get_tv_sec p

  ||| Reads the `tv_nsec` field of a `timespec` pointer.
  export %inline
  nsec : STimespec -> PrimIO NsecT
  nsec (TS p) = prim__get_tv_nsec p

  ||| Sets the `tv_sec` field of a `timespec` pointer.
  export %inline
  setSec : STimespec -> TimeT -> PrimIO ()
  setSec (TS p) t = prim__set_tv_sec p t

  ||| Sets the `tv_nsec` field of a `timespec` pointer.
  export %inline
  setNsec : STimespec -> NsecT -> PrimIO ()
  setNsec (TS p) t = prim__set_tv_nsec p t

  ||| Convert a `STimespec` to a `Clock t`
  export %inline
  toClock : {t : _} -> STimespec -> PrimIO (Clock t)
  toClock ts w =
    let MkIORes x0 w := sec ts w
        MkIORes x1 w := nsec ts w
     in MkIORes (MkClock (cast x0) (cast x1)) w

  export
  withTimespec : Clock t -> (STimespec -> EPrim a) -> EPrim a
  withTimespec cl f =
    withStruct STimespec $ \ts,w =>
      let MkIORes _ w := setSec ts (cast $ seconds cl) w
          MkIORes _ w := setNsec ts (cast $ nanoseconds cl) w
       in f ts w

--------------------------------------------------------------------------------
-- STimeval
--------------------------------------------------------------------------------

namespace Timeval

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
  sec : STimeval -> PrimIO TimeT
  sec s = get_timeval_tv_sec s.ptr

  export %inline
  usec : STimeval -> PrimIO SusecondsT
  usec s = get_timeval_tv_usec s.ptr

  export %inline
  setsec : STimeval -> TimeT -> PrimIO ()
  setsec s v = set_timeval_tv_sec s.ptr v

  export %inline
  setusec : STimeval -> SusecondsT -> PrimIO ()
  setusec s v = set_timeval_tv_usec s.ptr v

  ||| Pure alternative to the `STimeval` struct.
  public export
  record Timeval where
    constructor TV
    sec  : TimeT
    usec : SusecondsT

  %runElab derive "Timeval" [Show,Eq]

  export %inline
  stimeval : Timeval -> PrimIO STimeval
  stimeval (TV s u) = primMap STV $ prim__timeval s u

  export
  timeval : STimeval -> PrimIO Timeval
  timeval stv w =
    let MkIORes sec  w := Timeval.sec stv w
        MkIORes usec w := Timeval.usec stv w
     in MkIORes (TV sec usec) w

--------------------------------------------------------------------------------
-- Timerval
--------------------------------------------------------------------------------

namespace Timerval
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

  export %inline
  interval : Itimerval -> PrimIO STimeval
  interval s = primMap STV $ get_itimerval_it_interval s.ptr

  export %inline
  value : Itimerval -> PrimIO STimeval
  value s = primMap STV $ get_itimerval_it_value s.ptr

  export %inline
  setinterval : Itimerval -> STimeval -> PrimIO ()
  setinterval s v = set_itimerval_it_interval s.ptr v.ptr

  export %inline
  setvalue : Itimerval -> STimeval -> PrimIO ()
  setvalue s v = set_itimerval_it_value s.ptr v.ptr

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
  itimerval : Timerval -> PrimIO Itimerval
  itimerval (TRV (TV si ui) (TV sv uv)) = do
    primMap ITV $ prim__itimerval si ui sv uv

  export
  timerval : Itimerval -> PrimIO Timerval
  timerval itv w =
    let MkIORes siv  w := interval itv w
        MkIORes iv   w := timeval siv w
        MkIORes sval w := value itv w
        MkIORes val  w := timeval sval w
     in MkIORes (TRV iv val) w

--------------------------------------------------------------------------------
-- Timerspec
--------------------------------------------------------------------------------

namespace Timerspec
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
    interval : Itimerspec -> PrimIO STimespec
    interval s = primMap wrap $ get_itimerspec_it_interval s.ptr

    export %inline
    value : Itimerspec -> PrimIO STimespec
    value s = primMap wrap $ get_itimerspec_it_value s.ptr


    export %inline
    setinterval : Itimerspec -> STimespec -> PrimIO ()
    setinterval s v = set_itimerspec_it_interval s.ptr (unwrap v)

    export %inline
    setvalue : Itimerspec -> STimespec -> PrimIO ()
    setvalue s v = set_itimerspec_it_value s.ptr (unwrap v)

  ||| Creates and sets the fields of a `Itimerspec` pointer.
  |||
  ||| The allocated memory must be freed via `freeStruct`.
  export %inline
  itimerspec :
       (secInterval  : TimeT)
    -> (usecInterval : NsecT)
    -> (secValue     : TimeT)
    -> (usecValue    : NsecT)
    -> PrimIO Itimerspec
  itimerspec si ni sv nv = do
    primMap ITS $ prim__itimerspec si ni sv nv

  ||| Pure alternative to the `Itimerspec` struct.
  public export
  record Timerspec where
    constructor TS
    interval : Clock Duration
    value    : Clock Duration

  %runElab derive "Timerspec" [Show,Eq]

  export
  timerspec : Itimerspec -> PrimIO Timerspec
  timerspec its w =
    let MkIORes siv  w := Itimerspec.interval its w
        MkIORes iv   w := toClock siv w
        MkIORes sval w := Itimerspec.value its w
        MkIORes val  w := toClock sval w
     in MkIORes (TS iv val) w

  export
  duration : TimeT -> NsecT -> Clock Duration
  duration s ns = makeDuration (cast s) (cast ns)
