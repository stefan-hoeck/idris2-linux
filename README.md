# idris2-linux: Utilities for using Idris2 on GNU/Linux systems

Although it says "GNU/Linux" in the title, a lot of the stuff in here
might also work on other (POSIX) systems. That stuff should eventually
go to some kind of idris2-posix library. But it is now too early for
that.

This library is the result of working through the
[Linux Programming Interface](https://www.man7.org/tlpi/) and writing
bindings for the most important system calls in Idris. As I crawl
through the chapters, the todo list below will continuously grow.

## Chapter Overview

### Chapter 4

- [x] implement `open` plus flags and mode
- [x] implement `read` for raw buffers and `ByteString`
- [x] implement `write` for raw buffers and `ByteString`
- [x] implement `close`
- [x] implement `lseek` including different `whence` constants
- [x] solve exercises in Idris

### Chapter 5

- [x] get and set file flags using `fcntl`
- [x] implement file duplication: `dup`, `dup2`, and via `fcntl`
- [x] implement `pread` and `pwrite`
- [x] implement `truncate` and `ftruncate`
- [x] implement `mkstemp`
- [x] solve (most) exercises in Idris

The following will probably not be implemented:

* scatter and gather versions of `read` and `write`
* `tmpfile` as it operates on `FILE *`
* `dup3` as it is not part of POSIX

### Chapter 6

- [x] implement `getpid` and `getppid`.

The following will probably not be implemented:

* `setjmp` and `longjmp` as they belong strictly to C land
* exercises, as they deal either with non-implementable stuff or with the
  environment, and we already have that from base

### Chapter 7

- [ ] implement `realloc`

The following will probably not be implemented:

* `alloca` because it is mostly useful in C land
* `memalign` and `posix_memalign` because they are non-standard

### Chapter 8

Note: Calls to `crypt` are available from [idris2-crypt](https://github.com/stefan-hoeck/idris2-crypt).

The following will probably not be implemented:

* `getpwnam`, `getpwuid`, `getgrnam`, `getgruid`, `getpwent`, `setpwent`
  `endpwent`, `getspnam`, `getspent`, `setspent`, `endspent`: All of these
  can be implemented by reading or streaming the corresponding files in `/etc`
  into proper Idris records.

### Chapter 9

- [x] implement `getuid`, `geteuid`, `setuid`, and `seteuid`
- [x] implement `getgid`, `getegid`, `setgid`, and `setegid`
- [ ] implement `setreuid` and `setregid`
- [ ] implement `getgroups`
- [ ] implement `setgroups`
- [ ] implement `initgroups`

The following will probably not be implemented:

* `getresuid`, `getresgid`, `setfsuid`, and `setfsgid` (all are non-standard)

### Chapter 10

- [ ] implement `gmtime_r`
- [ ] implement `localtime_r`
- [ ] implement `mktime`
- [ ] implement `strftime_l`

The following will probably not be implemented:

* `settimeofday` and `adjtime` because these are typically handled by
  a system daemon

Note: Different types of clocks are implemented in `System.Clock` in base.

### Chapter 11

- [x] implement `sysconf`, `pathconf`, and `fpathconf`

### Chapter 12

- [ ] implement `uname`
- [x] solve process tree exercise

### Chapter 13

- [ ] implement `fileno`
- [ ] implement `fdopen`
- [ ] do the exercises

Notes: Currently, I am more interested in the raw system calls. Buffered
file I/O is available from `System.File` in base.

### Chapter 14

- [ ] implement `mount`
- [ ] implement `umount` and `umount2`
- [x] implement `statvfs` and `fstatvfs`
- [ ] do the exercise

### Chapter 15

- [x] implement `stat`, `lstat`, and `fstat`
- [ ] implement `utimes`, `futimes`, and `lutimes`
- [ ] implement `chown`, `lchown`, and `fchown`
- [ ] implement `umask`
- [ ] implement `chmod` and `fchmod`
- [ ] do the exercises

The following will probably not be implemented:

* `access` as its use is discouraged
* setting of i-node flags as these are non-standard

### Chapter 16

Extended attributes are non-standard and will not be supported
for the time being.

### Chapter 17

Access control lists are non-standard and will not be supported
for the time being.

### Chapter 18

- [x] implement `link` and `unlink`
- [x] implement `rename`
- [x] implement `symlink` and `readlink`
- [x] implement `mkidr`, `rmdir`, and something similar to `mkdir -p`
- [x] implement `remove`
- [x] implement `opendir` and `fopendir`
- [x] implement `rewinddir` and `closedir`
- [x] implement `readdir`
- [x] implement `getcwd`
- [x] implement `chdir`
- [x] implement `chroot`
- [ ] do the exercises

The following will probably not be implemented:

* `nfwt`: We should probably write our tree-walking routines in
  Idris proper instead of messing around with C callbacks.
* `realpath` because it's even more broken than `getcwd`

### Chapter 19

- [x] implement `inotify` utilities for monitoring files
- [ ] do the exercise

### Chapter 20

- [x] implement `kill` and `raise`
- [x] implement utilities for working with `sigset_t`
- [x] implement different versions of `sigprocmask`
- [x] implement `sigpending`

Notes: As per the Chez Scheme documentation, it is not safe to call from
C to Scheme from C interrupt handlers. We can therefore not make use
of `signal` and `sigaction` when on one of the Scheme backends.
~~Instead, a Scheme specific utility called `onsignal` is added for registering
signal handlers~~ (this is no longer available, as it caused spurious
core dumps). An alternative would be to use `epoll` with a signal
file descriptor (under Linux) or synchronous signal handling. See chapter 22.

### Chapter 21

- [x] implement `abort`

The following will probably not be implemented:

* `sigsetjmp` `siglongjmp`, and `sigaltstack` as I can't see their use on
  the default backends.

### Chapter 22

- [x] implement `sigsuspend`
- [x] implement `sigwaitinfo` and `sigtimedwait`
- [x] implement raising and handling of realtime signals
- [x] implement signal fetching via a file descriptor

### Chapter 23

- [x] implement `setitimerval` and `getitimerval`
- [x] implement `nanosleep` and `clock_nanosleep`.
- [x] implement `clock_gettime` and `clock_settime`
- [ ] add support for process and thread clock IDs
- [ ] implement POSIX clocks timers
- [x] implement timer handling via file descriptors

### Chapter 24

- [x] implement `fork`
- [x] add example applications with some IPC via signals

### Chapter 25

`exit` is already available in base.

The following will probably not be implemented:

* Installing exit handlers via `atexit` and `onexit`, as these might suffer
  the same limitations as other callbacks when used from Schemes.

### Chapter 26

- [x] implement `wait`
- [x] implement `waitpid`
- [x] implement `waitid`
- [ ] do the exercises

The following will probably not be implemented:

* `wait3` and `wait4` as they are (according to the book) not often used
  and lack standardization.

### Chapter 27

- [x] implement `execve` and related functions
- [x] implement `system`
- [ ] do the exercises
