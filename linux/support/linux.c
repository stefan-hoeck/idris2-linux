// Copyright 2024 Stefan Höck

#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/inotify.h>
#include <sys/stat.h>
#include <sys/statvfs.h>
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

void * li_inotify_next(void *ptr) {
  struct inotify_event *ev = (struct inotify_event *) ptr;
  return ptr + sizeof(struct inotify_event) + (ev->len);
}

uint32_t li_inotify_wd(struct inotify_event *ev) {
  return ev->wd;
}

uint32_t li_inotify_mask(struct inotify_event *ev) {
  return ev->mask;
}

uint32_t li_inotify_cookie(struct inotify_event *ev) {
  return ev->cookie;
}

uint32_t li_inotify_len(struct inotify_event *ev) {
  return ev->len;
}
