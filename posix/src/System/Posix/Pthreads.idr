module System.Posix.Pthreads

import System.Posix.Pthreads.Prim as P
import public Data.C.Ptr
import public System.Posix.Errno
import public System.Posix.Pthreads.Struct
import public System.Posix.Pthreads.Types
import System.Posix.Signal
import System.Posix.Time

%default total

||| Returns the thread ID of the current thread.
export %inline
pthreadSelf : HasIO io => io PthreadT
pthreadSelf = primIO P.pthreadSelf

||| Blocks the current thread and waits for the given thread to terminate.
export %inline
pthreadJoin : ErrIO io => PthreadT -> io ()
pthreadJoin p = eprim (P.pthreadJoin p)

||| Allocates and initializes a new mutex of the given type.
|||
||| This must be freed with `destroyMutex`.
export
mkmutex : ErrIO io => MutexType -> io MutexT
mkmutex t = eprim (P.mkmutex t)

||| Destroys a mutex and frees the memory allocated for it.
export %inline
destroyMutex : HasIO io => MutexT -> io ()
destroyMutex m = primIO (P.destroyMutex m)

||| Tries to lock the given mutex, blocking the calling thread
||| in case it is already locked.
export %inline
lockMutex : ErrIO io => MutexT -> io ()
lockMutex p = eprim (P.lockMutex p)

||| Like `lockMutex` but returns a boolean with `False` indicating
||| that the lock timed out
export
timedlockMutex : ErrIO io => MutexT -> Clock Duration -> io Bool
timedlockMutex p cl = eprim (P.timedlockMutex p cl)

||| Like `lockMutex` but returns `False` in case the mutex is
||| already locked.
export
trylockMutex : ErrIO io => MutexT -> io Bool
trylockMutex p = eprim (P.trylockMutex p)

||| Unlocks the given mutex.
|||
||| This is an error if the calling thread is not the one holding
||| the mutex's lock.
export %inline
unlockMutex : ErrIO io => MutexT -> io ()
unlockMutex p = eprim (P.unlockMutex p)

--------------------------------------------------------------------------------
-- CondT
--------------------------------------------------------------------------------

||| Allocates and initializes a new condition variable.
|||
||| This must be freed with `destroyCond`.
export %inline
mkcond : ErrIO io => io CondT
mkcond = eprim P.mkcond

||| Destroys a condition variable and frees the memory allocated for it.
export %inline
destroyCond : HasIO io => CondT -> io ()
destroyCond = primIO . destroyCond

||| Signals the given `pthread_cond_t`.
|||
||| If several threads are waiting on the condition, it is unspecified
||| which of them will be signalled. We are only guaranteed that at least
||| of them will be woken up.
export %inline
condSignal : ErrIO io => CondT -> io ()
condSignal = eprim . condSignal

||| Broadcasts the given `pthread_cond_t`.
|||
||| This will wake up all threads waiting on the given condition.
export %inline
condBroadcast : ErrIO io => CondT -> io ()
condBroadcast = eprim . condBroadcast

||| Blocks the given thread and waits for the given condition to
||| be signalled.
|||
||| Note: The mutex must have been locked by the calling thread. The
||| lock is automatically released upon calling `condWait`, and when
||| the thread is woken up, the mutex will automatically be locked again.
export %inline
condWait : ErrIO io => CondT -> MutexT -> io ()
condWait c = eprim . condWait c

||| Like `condWait` but will return `False` in case the operation timed out.
export %inline
condTimedwait : ErrIO io => CondT -> MutexT -> Clock Duration -> io Bool
condTimedwait c m = eprim . condTimedwait c m

--------------------------------------------------------------------------------
-- Thread Cancelation
--------------------------------------------------------------------------------

||| Sends a cancelation request to the given thread.
export %inline
pthreadCancel : ErrIO io => PthreadT -> io ()
pthreadCancel = eprim . P.pthreadCancel

||| Tests for thread cancelation in the absence of other cancelation
||| points.
export %inline
pthreadTestCancel : HasIO io => io ()
pthreadTestCancel = primIO P.pthreadTestCancel

||| Sets the current thread's cancel type returning the previous cancel type.
export %inline
setCancelType : HasIO io => CancelType -> io CancelType
setCancelType = primIO . P.setCancelType

||| Sets the current thread's cancel state returning the previous cancel state.
export %inline
setCancelState : HasIO io => CancelState -> io CancelState
setCancelState = primIO . P.setCancelState

--------------------------------------------------------------------------------
-- Signals and Threads
--------------------------------------------------------------------------------

||| Adjust the thread's signal mask according to the given `How`
||| and signal set.
export %inline
pthreadSigmask : ErrIO io => How -> List Signal -> io ()
pthreadSigmask h = eprim . P.pthreadSigmask h

||| Returns the current signal mask of the thread.
|||
||| Note: This allocates a new `sigset_t` pointer and returns the
|||       previously set signal mask. Client code is responsible to
|||       free the memory for this once it is no longer used.
export %inline
pthreadSiggetmask : HasIO io => io SigsetT
pthreadSiggetmask = primIO P.pthreadSiggetmask


||| Sends the given signal to the given thread.
export %inline
pthreadKill : ErrIO io => PthreadT -> Signal -> io ()
pthreadKill t = eprim . P.pthreadKill t
