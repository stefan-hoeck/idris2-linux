// Copyright 2024 Stefan Höck

#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <unistd.h>

uint32_t li_errno() { return errno; }

ssize_t li_write(int fd, char *buf, size_t off, size_t bytes) {
  return write(fd, buf + off, bytes);
}
