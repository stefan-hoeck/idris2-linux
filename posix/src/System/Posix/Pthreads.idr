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
pthreadJoin : Has Errno es => EIO1 f => PthreadT -> f es ()
pthreadJoin p = elift1 (P.pthreadJoin p)

||| Allocates and initializes a new mutex of the given type.
|||
||| This must be freed with `destroyMutex`.
export
mkmutex : Has Errno es => EIO1 f => MutexType -> f es MutexT
mkmutex t = elift1 (P.mkmutex t)

||| Destroys a mutex and frees the memory allocated for it.
export %inline
destroyMutex : HasIO io => MutexT -> io ()
destroyMutex m = primIO (P.destroyMutex m)

||| Tries to lock the given mutex, blocking the calling thread
||| in case it is already locked.
export %inline
lockMutex : Has Errno es => EIO1 f => MutexT -> f es ()
lockMutex p = elift1 (P.lockMutex p)

||| Like `lockMutex` but returns a boolean with `False` indicating
||| that the lock timed out
export
timedlockMutex : Has Errno es => EIO1 f => MutexT -> Clock Duration -> f es Bool
timedlockMutex p cl = elift1 (P.timedlockMutex p cl)

||| Like `lockMutex` but returns `False` in case the mutex is
||| already locked.
export
trylockMutex : Has Errno es => EIO1 f => MutexT -> f es Bool
trylockMutex p = elift1 (P.trylockMutex p)

||| Unlocks the given mutex.
|||
||| This is an error if the calling thread is not the one holding
||| the mutex's lock.
export %inline
unlockMutex : Has Errno es => EIO1 f => MutexT -> f es ()
unlockMutex p = elift1 (P.unlockMutex p)

--------------------------------------------------------------------------------
-- CondT
--------------------------------------------------------------------------------

||| Allocates and initializes a new condition variable.
|||
||| This must be freed with `destroyCond`.
export %inline
mkcond : Has Errno es => EIO1 f => f es CondT
mkcond = elift1 P.mkcond

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
condSignal : Has Errno es => EIO1 f => CondT -> f es ()
condSignal c = elift1 (condSignal c)

||| Broadcasts the given `pthread_cond_t`.
|||
||| This will wake up all threads waiting on the given condition.
export %inline
condBroadcast : Has Errno es => EIO1 f => CondT -> f es ()
condBroadcast c = elift1 (condBroadcast c)

||| Blocks the given thread and waits for the given condition to
||| be signalled.
|||
||| Note: The mutex must have been locked by the calling thread. The
||| lock is automatically released upon calling `condWait`, and when
||| the thread is woken up, the mutex will automatically be locked again.
export %inline
condWait : Has Errno es => EIO1 f => CondT -> MutexT -> f es ()
condWait c m = elift1 (condWait c m)

||| Like `condWait` but will return `False` in case the operation timed out.
export %inline
condTimedwait : Has Errno es => EIO1 f => CondT -> MutexT -> Clock Duration -> f es Bool
condTimedwait c m d = elift1 (condTimedwait c m d)

--------------------------------------------------------------------------------
-- Thread Cancelation
--------------------------------------------------------------------------------

||| Sends a cancelation request to the given thread.
export %inline
pthreadCancel : Has Errno es => EIO1 f => PthreadT -> f es ()
pthreadCancel t = elift1 (P.pthreadCancel t)

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
pthreadSigmask : Has Errno es => EIO1 f => How -> List Signal -> f es ()
pthreadSigmask h ss = elift1 (P.pthreadSigmask h ss)

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
pthreadKill : Has Errno es => EIO1 f => PthreadT -> Signal -> f es ()
pthreadKill t s = elift1 (P.pthreadKill t s)
