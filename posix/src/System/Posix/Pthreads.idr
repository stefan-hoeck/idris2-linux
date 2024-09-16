module System.Posix.Pthreads

import public Data.C.Ptr
import public System.Posix.Errno
import public System.Posix.Pthreads.Types
import System.Posix.Signal
import System.Posix.Time

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:pthread_equal, posix-idris"
prim__pthread_equal : AnyPtr -> AnyPtr -> Bits8

%foreign "C:pthread_self, posix-idris"
prim__pthread_self : PrimIO AnyPtr

%foreign "C:li_pthread_join, posix-idris"
prim__pthread_join : AnyPtr -> PrimIO Bits32

%foreign "C:li_pthread_mutex_init, posix-idris"
prim__pthread_mutex_init : AnyPtr -> Bits8 -> PrimIO Bits32

%foreign "C:li_pthread_mutex_destroy, posix-idris"
prim__pthread_mutex_destroy : AnyPtr -> PrimIO ()

%foreign "C:pthread_mutex_lock, posix-idris"
prim__pthread_mutex_lock : AnyPtr -> PrimIO Bits32

%foreign "C:pthread_mutex_trylock, posix-idris"
prim__pthread_mutex_trylock : AnyPtr -> PrimIO Bits32

%foreign "C:pthread_mutex_timedlock, posix-idris"
prim__pthread_mutex_timedlock : AnyPtr -> AnyPtr -> PrimIO Bits32

%foreign "C:pthread_mutex_unlock, posix-idris"
prim__pthread_mutex_unlock : AnyPtr -> PrimIO Bits32

%foreign "C:li_pthread_cond_init, posix-idris"
prim__pthread_cond_init : AnyPtr -> PrimIO Bits32

%foreign "C:li_pthread_cond_destroy, posix-idris"
prim__pthread_cond_destroy : AnyPtr -> PrimIO ()

%foreign "C:pthread_cond_signal, posix-idris"
prim__pthread_cond_signal : AnyPtr -> PrimIO Bits32

%foreign "C:pthread_cond_broadcast, posix-idris"
prim__pthread_cond_broadcast : AnyPtr -> PrimIO Bits32

%foreign "C:pthread_cond_wait, posix-idris"
prim__pthread_cond_wait : AnyPtr -> AnyPtr -> PrimIO Bits32

%foreign "C:pthread_cond_timedwait, posix-idris"
prim__pthread_cond_timedwait : AnyPtr -> AnyPtr -> AnyPtr -> PrimIO Bits32

%foreign "C:pthread_cancel, posix-idris"
prim__pthread_cancel : AnyPtr -> PrimIO Bits32

%foreign "C:pthread_testcancel, posix-idris"
prim__pthread_testcancel : PrimIO ()

%foreign "C:li_pthread_setcanceltype, posix-idris"
prim__pthread_setcanceltype : Bits8 -> PrimIO Bits8

%foreign "C:li_pthread_setcancelstate, posix-idris"
prim__pthread_setcancelstate : Bits8 -> PrimIO Bits8

%foreign "C:li_pthread_sigmask1, posix-idris"
prim__pthread_sigmask1 : Bits8 -> AnyPtr -> PrimIO ()

%foreign "C:li_pthread_sigmask, posix-idris"
prim__pthread_sigmask : Bits8 -> AnyPtr -> PrimIO AnyPtr

%foreign "C:li_pthread_siggetmask, posix-idris"
prim__pthread_siggetmask : PrimIO AnyPtr

%foreign "C:pthread_kill, posix-idris"
prim__pthread_kill : AnyPtr -> Bits32 -> PrimIO Bits32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Wrapper around an identifier for a POSIX thread.
export
record PthreadT where
  constructor P
  ptr : AnyPtr

||| Returns the thread ID of the current thread.
export %inline
pthreadSelf : HasIO io => io PthreadT
pthreadSelf = primIO $ primMap P $ prim__pthread_self

||| Blocks the current thread and waits for the given thread to terminate.
export %inline
pthreadJoin : PthreadT -> IO (Either Errno ())
pthreadJoin p = posToUnit $ prim__pthread_join p.ptr

export %inline
Eq PthreadT where
  x == y = toBool (prim__pthread_equal x.ptr y.ptr)

||| Warning: This `Show` implementation for thread IDs is for debugging only!
||| According to SUSv3, a thread ID need not be a scalar, so it should be
||| treated as an opaque type.
|||
||| On many implementations (including on Linux), they are just integers, so
||| this can be useful for debugging.
export %inline
Show PthreadT where
  show (P p) = show (believe_me {b = Bits64} p)

--------------------------------------------------------------------------------
-- MutexT
--------------------------------------------------------------------------------

||| Wrapper around a `pthread_mutex_t` pointer.
|||
||| Noted: While this provides additional flexibility over the type of mutex
||| we use (see `mkmutex`) and how we acquire a lock on a mutex, it is less
||| convenient to use than the garbage-collected version from
||| `System.Concurrency`.
export
record MutexT where
  constructor M
  ptr : AnyPtr

%inline
Struct MutexT where
  unwrap = ptr
  wrap   = M

%inline
SizeOf MutexT where sizeof_ = mutex_t_size

||| Allocates and initializes a new mutex of the given type.
|||
||| This must be freed with `destroyMutex`.
export
mkmutex : MutexType -> IO (Either Errno MutexT)
mkmutex t = do
  m <- allocStruct MutexT
  e <- posToUnit $ prim__pthread_mutex_init m.ptr (mutexCode t)
  case e of
    Left x  => freeStruct m $> Left x
    Right () => pure (Right m)

||| Destroys a mutex and frees the memory allocated for it.
export %inline
destroyMutex : HasIO io => MutexT -> io ()
destroyMutex m = primIO $ prim__pthread_mutex_destroy m.ptr

||| Tries to lock the given mutex, blocking the calling thread
||| in case it is already locked.
export %inline
lockMutex : MutexT -> IO (Either Errno ())
lockMutex p = posToUnit $ prim__pthread_mutex_lock p.ptr

export %inline
timedlockMutex : MutexT -> Timespec -> IO (Either Errno ())
timedlockMutex p t = posToUnit $ prim__pthread_mutex_timedlock p.ptr (unwrap t)

||| Like `lockMutex` but fails with `EBUSY` in case the mutex is
||| already locked.
export %inline
trylockMutex : MutexT -> IO (Either Errno ())
trylockMutex p = posToUnit $ prim__pthread_mutex_trylock p.ptr

||| Unlocks the given mutex.
|||
||| This is an error if the calling thread is not the one holding
||| the mutex's lock.
export %inline
unlockMutex : MutexT -> IO (Either Errno ())
unlockMutex p = posToUnit $ prim__pthread_mutex_unlock p.ptr

--------------------------------------------------------------------------------
-- CondT
--------------------------------------------------------------------------------

||| Wrapper around a `pthread_cond_t` pointer.
|||
||| Noted: While this provides additional flexibility over the type of condition
||| we use (see `mkcond`) convenient to use than the garbage-collected version from
||| `System.Concurrency`.
export
record CondT where
  constructor C
  ptr : AnyPtr

%inline
Struct CondT where
  unwrap = ptr
  wrap   = C

%inline
SizeOf CondT where sizeof_ = cond_t_size

||| Allocates and initializes a new condition variable.
|||
||| This must be freed with `destroyCond`.
export
mkcond : IO (Either Errno CondT)
mkcond = do
  m <- allocStruct CondT
  e <- posToUnit $ prim__pthread_cond_init m.ptr
  case e of
    Left x   => freeStruct m $> Left x
    Right () => pure (Right m)

||| Destroys a condition variable and frees the memory allocated for it.
export %inline
destroyCond : HasIO io => CondT -> io ()
destroyCond m = primIO $ prim__pthread_cond_destroy m.ptr

||| Signals the given `pthread_cond_t`.
|||
||| If several threads are waiting on the condition, it is unspecified
||| which of them will be signalled. We are only guaranteed that at least
||| of them will be woken up.
export %inline
condSignal : CondT -> IO (Either Errno ())
condSignal p = posToUnit $ prim__pthread_cond_signal p.ptr

||| Broadcasts the given `pthread_cond_t`.
|||
||| This will wake up all threads waiting on the given condition.
export %inline
condBroadcast : CondT -> IO (Either Errno ())
condBroadcast p = posToUnit $ prim__pthread_cond_broadcast p.ptr

||| Blocks the given thread and waits for the given condition to
||| be signalled.
|||
||| Note: The mutex must have been locked by the calling thread. The
||| lock is automatically released upon calling `condWait`, and when
||| the thread is woken up, the mutex will automatically be locked again.
export %inline
condWait : CondT -> MutexT -> IO (Either Errno ())
condWait p m = posToUnit $ prim__pthread_cond_wait p.ptr m.ptr

||| Like `condWait` but will return with `ETIMEDOUT` after the given
||| time interval expires.
export %inline
condTimedwait : CondT -> MutexT -> Timespec -> IO (Either Errno ())
condTimedwait p m t =
  posToUnit $ prim__pthread_cond_timedwait p.ptr m.ptr (unwrap t)

--------------------------------------------------------------------------------
-- Thread Cancelation
--------------------------------------------------------------------------------

toTpe : Bits8 -> CancelType
toTpe b =
  if b == cancelType CANCEL_DEFERRED then CANCEL_DEFERRED else CANCEL_ASYNCHRONOUS

toState : Bits8 -> CancelState
toState b =
  if b == cancelState CANCEL_ENABLE then CANCEL_ENABLE else CANCEL_DISABLE

||| Sends a cancelation request to the given thread.
export %inline
pthreadCancel : PthreadT -> IO (Either Errno ())
pthreadCancel t = posToUnit $ prim__pthread_cancel t.ptr

||| Tests for thread cancelation in the absence of other cancelation
||| points.
export %inline
pthreadTestCancel : HasIO io => io ()
pthreadTestCancel = primIO prim__pthread_testcancel

||| Sets the current thread's cancel type returning the previous cancel type.
export %inline
setCancelType : HasIO io => CancelType -> io CancelType
setCancelType t =
  primIO $ primMap toTpe $ prim__pthread_setcanceltype (cancelType t)

||| Sets the current thread's cancel state returning the previous cancel state.
export %inline
setCancelState : HasIO io => CancelState -> io CancelState
setCancelState t =
  primIO $ primMap toState $ prim__pthread_setcancelstate (cancelState t)

--------------------------------------------------------------------------------
-- Signals and Threads
--------------------------------------------------------------------------------

||| Adjust the thread's signal mask according to the given `How`
||| and signal set.
|||
||| Note: This allocates a new `sigset_t` pointer and returns the
|||       previously set signal mask. Client code is responsible to
|||       free the memory for this once it is no longer used.
|||       See also `pthreadSigmask'` for a version that does not return
|||       the previous signal mask.
export %inline
pthreadSigmask : HasIO io => How -> SigsetT -> io SigsetT
pthreadSigmask h p =
  primIO $ \w =>
    let MkIORes p2 w := prim__pthread_sigmask (howCode h) (unwrap p) w
     in MkIORes (wrap p2) w

||| Like `sigprocmask` but does not allocate a pointer for the
||| previous `sigset_t`.
export %inline
pthreadSigmask' : HasIO io => How -> SigsetT -> io ()
pthreadSigmask' h p = primIO $ prim__pthread_sigmask1 (howCode h) (unwrap p)

||| Returns the current signal mask of the thread.
|||
||| Note: This allocates a new `sigset_t` pointer and returns the
|||       previously set signal mask. Client code is responsible to
|||       free the memory for this once it is no longer used.
export %inline
pthreadSiggetmask : HasIO io => io SigsetT
pthreadSiggetmask =
  primIO $ \w =>
    let MkIORes p w := prim__pthread_siggetmask w
     in MkIORes (wrap p) w

||| Sends the given signal to the given thread.
export %inline
pthreadKill : PthreadT -> Signal -> IO (Either Errno ())
pthreadKill t s = posToUnit $ prim__pthread_kill t.ptr s.sig
