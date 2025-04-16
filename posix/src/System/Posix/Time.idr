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

--------------------------------------------------------------------------------
-- Tm
--------------------------------------------------------------------------------

namespace STm
  export %foreign "C:get_tm_sec, posix-idris"
  get_tm_sec: AnyPtr -> PrimIO Bits8

  export %foreign "C:get_tm_min, posix-idris"
  get_tm_min: AnyPtr -> PrimIO Bits8

  export %foreign "C:get_tm_hour, posix-idris"
  get_tm_hour: AnyPtr -> PrimIO Bits8

  export %foreign "C:get_tm_mday, posix-idris"
  get_tm_mday: AnyPtr -> PrimIO Bits8

  export %foreign "C:get_tm_mon, posix-idris"
  get_tm_mon: AnyPtr -> PrimIO Bits8

  export %foreign "C:get_tm_year, posix-idris"
  get_tm_year: AnyPtr -> PrimIO Int32

  export %foreign "C:get_tm_wday, posix-idris"
  get_tm_wday: AnyPtr -> PrimIO Bits8

  export %foreign "C:get_tm_yday, posix-idris"
  get_tm_yday: AnyPtr -> PrimIO Bits16

  export %foreign "C:get_tm_isdst, posix-idris"
  get_tm_isdst: AnyPtr -> PrimIO Int8

  export %foreign "C:li_gmtime_r, posix-idris"
  prim__gmtime_r: TimeT -> AnyPtr -> PrimIO ()

  export %foreign "C:li_localtime_r, posix-idris"
  prim__localtime_r: TimeT -> AnyPtr -> PrimIO ()

  ||| Converts time to a nicely formatted string.
  export %foreign "C:li_ctime_r, posix-idris"
  ctime: TimeT -> String

  export %foreign "C:li_asctime_r, posix-idris"
  prim__asctime_r: (sec,min,hour,mday,mon : Bits8) -> (year : Int32) -> (wday : Bits8) -> (yday : Bits16) -> (isdst : Int8) -> String

  export %foreign "C:li_mktime, posix-idris"
  prim__mktime: (sec,min,hour,mday,mon : Bits8) -> (year : Int32) -> (wday : Bits8) -> (yday : Bits16) -> (isdst : Int8) -> TimeT

  ||| Note: Although this is POSIX compliant, it is not available on
  ||| MacOS (Darwin). Idris programs making use of this might fail on
  ||| Darwin during code generation.
  export
  record STm s where
    constructor STM
    ptr : AnyPtr

  export %inline
  Struct STm where
    swrap   = STM
    sunwrap = ptr

  export %inline
  SizeOf (STm s) where
    sizeof_ = tm_size

  export %inline
  getsec: STm s -> F1 s Bits8
  getsec (STM ptr) = ffi $ get_tm_sec ptr

  export %inline
  getmin: STm s -> F1 s Bits8
  getmin (STM ptr) = ffi $ get_tm_min ptr

  export %inline
  gethour: STm s -> F1 s Bits8
  gethour (STM ptr) = ffi $ get_tm_hour ptr

  export %inline
  getmday: STm s -> F1 s Bits8
  getmday (STM ptr) = ffi $ get_tm_mday ptr

  export %inline
  getmon: STm s -> F1 s Bits8
  getmon (STM ptr) = ffi $ get_tm_mon ptr

  export %inline
  getyear: STm s -> F1 s Int32
  getyear (STM ptr) = ffi $ get_tm_year ptr

  export %inline
  getwday: STm s -> F1 s Bits8
  getwday (STM ptr) = ffi $ get_tm_wday ptr

  export %inline
  getyday: STm s -> F1 s Bits16
  getyday (STM ptr) = ffi $ get_tm_yday ptr

  export %inline
  getisdst: STm s -> F1 s Int8
  getisdst (STM ptr) = ffi $ get_tm_isdst ptr

  ||| Pure alternative to the `STm` struct.
  |||
  ||| Dissection of a `Clock t` into its time components.
  public export
  record Tm where
    constructor TM
    ||| Second of minute (0 - 60; could be a leap second)
    sec:   Bits8

    ||| Minute of hour (0 - 59)
    min:   Bits8

    ||| Hour of day (0 - 23)
    hour:  Bits8

    ||| Day of month (1 - 31)
    mday:  Bits8

    ||| Month (0 - 11)
    mon:   Bits8

    ||| Year since 1900
    year:  Int32

    ||| Day of week (Sunday = 0)
    wday:  Bits8

    ||| Day of year (0 - 365; 1 Jan = 0)
    yday:  Bits16

    ||| `True` if daylight safing time is active
    isdst: Bool

  %runElab derive "Tm" [Show,Eq]

  export
  tm : STm s -> F1 s Tm
  tm stm t =
    let s  # t := getsec stm t
        m  # t := getmin stm t
        h  # t := gethour stm t
        md # t := getmday stm t
        mo # t := getmon stm t
        y  # t := getyear stm t
        wd # t := getwday stm t
        yd # t := getyday stm t
        id # t := getisdst stm t
     in TM s m h md mo y wd yd (id > 0) # t

  export %inline %hint
  convTm : Convert Tm
  convTm = convStruct STm tm

  withSTm : (forall s . STm s -> F1 s a) -> a
  withSTm f =
    run1 $ \t =>
     let stm # t := allocStruct1 STm t
         res # t := f stm t
         _   # t := freeStruct1 stm t
      in res # t

  ||| Converts time in seconds since the Epoch to broken down UTC time.
  export
  gmtime : TimeT -> Tm
  gmtime secs =
    withSTm $ \stm,t =>
     let _   # t := ffi (prim__gmtime_r secs (sunwrap stm)) t
      in tm stm t

  ||| Converts time in seconds since the Epoch to broken down local time.
  export
  localtime : TimeT -> Tm
  localtime secs =
    withSTm $ \stm,t =>
     let _   # t := ffi (prim__localtime_r secs (sunwrap stm)) t
      in tm stm t

  ||| Converts a UTC clock value to broken down local time.
  export %inline
  fromUTC : Clock UTC -> Tm
  fromUTC = localtime . cast . seconds

  ||| Converts time to a nicely formatted string.
  export
  asctime : Tm -> String
  asctime (TM sec min hour mday mon year wday yday isdst) =
    prim__asctime_r sec min hour mday mon year wday yday (if isdst then 1 else 0)

  ||| Converts a broken down time to seconds since the Epoch.
  export
  mktime : Tm -> TimeT
  mktime (TM sec min hour mday mon year wday yday isdst) =
    prim__mktime sec min hour mday mon year wday yday (if isdst then 1 else 0)

  ||| Converts broken down local time to a UTC clock time.
  export %inline
  toUTC : Tm -> Clock UTC
  toUTC = fromNano . (* 1_000_000_000) . cast . mktime

  ||| Keeps only the hours, seconds, and minutes of a broken down time.
  export
  seconds : Tm -> Integer
  seconds tm = cast tm.sec + cast tm.min * 60 + cast tm.hour * 3600

  ||| Drops the hours, seconds, and minutes from a broken down time.
  export
  dateOnly : Tm -> Tm
  dateOnly = {sec := 0, min := 0, hour := 0}
