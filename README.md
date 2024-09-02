# idris2-linux: Utilities for using Idris2 on GNU/Linux systems

Although it says "GNU/Linux" in the title, a lot of the stuff in here
might also work on other (POSIX) systems. That stuff should eventually
go to some kind of idris2-posix library. But it is now too early for
that.

This library is the result of working through the
[Linux Programming Interface](https://www.man7.org/tlpi/) and writing
bindings for the most important system calls in Idris. As I crawl
through the chapters, the todo list below will continuously grow.

## Missing Stuff

### Chapter 4

- [x] Implement `open` plus flags and mode
- [x] Implement `read` for raw buffers and `ByteString`
- [x] Implement `write` for raw buffers and `ByteString`
- [x] Implement `close`
- [x] Implement `lseek` including different `whence` constants
- [x] Solve exercises in Idris
