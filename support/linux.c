// Copyright 2024 Stefan Höck

#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <unistd.h>

#define CHECKRES                                                               \
  if (res == -1) {                                                             \
    return -errno;                                                             \
  } else {                                                                     \
    return res;                                                                \
  }

uint32_t li_errno() { return errno; }

int li_open(const char *name, int flags, mode_t mode) {
  int res = open(name, flags, mode);
  CHECKRES
}

int li_close(int fd) {
  int res = close(fd);
  CHECKRES
}

ssize_t li_read(int fd, char *buf, size_t bytes) {
  int res = read(fd, buf, bytes);
  CHECKRES
}

ssize_t li_write(int fd, char *buf, size_t off, size_t bytes) {
  int res = write(fd, buf + off, bytes);
  CHECKRES
}

int li_set_flags(int fd, int flags) {
  int res = fcntl(fd, F_SETFL, flags);
  CHECKRES
}

int li_get_flags(int fd) {
  int res = fcntl(fd, F_GETFL);
  CHECKRES
}
