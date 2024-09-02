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

- [ ] implement `getpwnam` or its reentrant analogue
- [ ] implement `getpwuid` or its reentrant analogue
- [ ] implement `getgrnam` or its reentrant analogue
- [ ] implement `getgruid` or its reentrant analogue
- [ ] implement `getpwent`, `setpwent`, and `endpwent`
- [ ] implement `getspnam` or its reentrant analogue
- [ ] implement `getspent`, `setspent`, and `endspent`

Note: Calls to `crypt` are available from [idris2-crypt](https://github.com/stefan-hoeck/idris2-crypt).
