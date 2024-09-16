// Copyright 2024 Stefan Höck

#define _GNU_SOURCE 1

#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <string.h>
#include <pthread.h>
#include <sys/inotify.h>
#include <sys/signalfd.h>
#include <sys/stat.h>
#include <sys/statvfs.h>
#include <sys/timerfd.h>
#include <unistd.h>

#define CHECKRES                                                               \
  if (res == -1) {                                                             \
    return -errno;                                                             \
  } else {                                                                     \
    return res;                                                                \
  }

int li_inotify_init1(int flags) {
  int res = inotify_init1(flags);
  CHECKRES
}

int li_inotify_add_watch(int fd, const char *pth, uint32_t mask) {
  int res = inotify_add_watch(fd, pth, mask);
  CHECKRES
}

int li_inotify_rm(int fd, int wd) {
  int res = inotify_rm_watch(fd, wd);
  CHECKRES
}

uint32_t li_inotify_more(void *buf, void *ptr, int numread) {
  if (ptr < buf + numread) {
    return 1;
  } else {
    return 0;
  }
}

void *li_inotify_next(void *ptr) {
  struct inotify_event *ev = (struct inotify_event *)ptr;
  return ptr + sizeof(struct inotify_event) + (ev->len);
}

uint32_t li_inotify_wd(struct inotify_event *ev) { return ev->wd; }

uint32_t li_inotify_mask(struct inotify_event *ev) { return ev->mask; }

uint32_t li_inotify_cookie(struct inotify_event *ev) { return ev->cookie; }

uint32_t li_inotify_len(struct inotify_event *ev) { return ev->len; }

////////////////////////////////////////////////////////////////////////////////
// signalfd
////////////////////////////////////////////////////////////////////////////////

int li_signalfd(const sigset_t *mask, int flags) {
  int res = signalfd(-1, mask, flags);
  CHECKRES
}

uint32_t li_ssi_signo(struct signalfd_siginfo *i) { return i->ssi_signo; }

int32_t li_ssi_errno(struct signalfd_siginfo *i) { return i->ssi_errno; }

int32_t li_ssi_code(struct signalfd_siginfo *i) { return i->ssi_code; }

uint32_t li_ssi_pid(struct signalfd_siginfo *i) { return i->ssi_pid; }

uint32_t li_ssi_uid(struct signalfd_siginfo *i) { return i->ssi_uid; }

int32_t li_ssi_fd(struct signalfd_siginfo *i) { return i->ssi_fd; }

uint32_t li_ssi_tid(struct signalfd_siginfo *i) { return i->ssi_tid; }

uint32_t li_ssi_band(struct signalfd_siginfo *i) { return i->ssi_band; }

uint32_t li_ssi_overrun(struct signalfd_siginfo *i) { return i->ssi_overrun; }

uint32_t li_ssi_trapno(struct signalfd_siginfo *i) { return i->ssi_trapno; }

int32_t li_ssi_status(struct signalfd_siginfo *i) { return i->ssi_status; }

int32_t li_ssi_int(struct signalfd_siginfo *i) { return i->ssi_int; }

uint64_t li_ssi_ptr(struct signalfd_siginfo *i) { return i->ssi_ptr; }

uint64_t li_ssi_utime(struct signalfd_siginfo *i) { return i->ssi_utime; }

uint64_t li_ssi_stime(struct signalfd_siginfo *i) { return i->ssi_stime; }

uint64_t li_ssi_addr(struct signalfd_siginfo *i) { return i->ssi_addr; }

uint16_t li_ssi_addr_lsb(struct signalfd_siginfo *i) { return i->ssi_addr_lsb; }

////////////////////////////////////////////////////////////////////////////////
// timerfd
////////////////////////////////////////////////////////////////////////////////

int li_timerfd_create(int clockid, int flags) {
  int res = timerfd_create(clockid, flags);
  CHECKRES
}

int li_timerfd_settime(int fd, int flags, struct itimerspec *new,
                       struct itimerspec *old) {
  int res = timerfd_settime(fd, flags, new, old);
  CHECKRES
}

int li_timerfd_settime1(int fd, int flags, struct itimerspec *new) {
  return li_timerfd_settime(fd, flags, new, NULL);
}

int li_timerfd_gettime(int fd, struct itimerspec *old) {
  int res = timerfd_gettime(fd, old);
  CHECKRES
}

int64_t li_timerfd_read(int fd) {
  uint64_t val;
  int res = read(fd, &val, 8);
  if (res == -1) {
    return -errno;
  } else {
    return val;
  }
}

////////////////////////////////////////////////////////////////////////////////
// pthreads
////////////////////////////////////////////////////////////////////////////////

uint32_t li_pthread_sigqueue(pthread_t p, int sig, int word) {
  union sigval u = {.sival_int = word};
  return pthread_sigqueue(p, sig, u);
}
