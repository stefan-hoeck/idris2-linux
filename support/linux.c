// Copyright 2024 Stefan Höck

#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/statvfs.h>
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

int li_dup(int fd) {
  int res = dup(fd);
  CHECKRES
}

int li_dup2(int fd, int dst) {
  int res = dup2(fd, dst);
  CHECKRES
}

int li_dupfd(int fd, int startfd) {
  int res = fcntl(fd, F_DUPFD, startfd);
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

ssize_t li_pread(int fd, char *buf, size_t bytes, off_t off) {
  int res = pread(fd, buf, bytes, off);
  CHECKRES
}

ssize_t li_write(int fd, char *buf, size_t off, size_t bytes) {
  int res = write(fd, buf + off, bytes);
  CHECKRES
}

ssize_t li_pwrite(int fd, char *buf, size_t offset, size_t bytes, off_t off) {
  int res = pwrite(fd, buf + offset, bytes, off);
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

int li_ftruncate(int fd, off_t len) {
  int res = ftruncate(fd, len);
  CHECKRES
}

int li_truncate(const char *path, off_t len) {
  int res = truncate(path, len);
  CHECKRES
}

int li_mkstemp(char *path) {
  int res = mkstemp(path);
  CHECKRES
}

int li_setuid(uid_t uid) {
  int res = setuid(uid);
  CHECKRES
}

int li_setgid(gid_t gid) {
  int res = setgid(gid);
  CHECKRES
}

int li_seteuid(uid_t uid) {
  int res = seteuid(uid);
  CHECKRES
}

int li_setegid(gid_t gid) {
  int res = setegid(gid);
  CHECKRES
}

struct statvfs *li_allocStatvfs() {
  return (struct statvfs *)calloc(1, sizeof(struct statvfs));
}

void *li_freeStatvfs(struct statvfs *v) { free(v); }

struct stat *li_allocStat() {
  return (struct stat *)calloc(1, sizeof(struct stat));
}

void *li_freeStat(struct stat *v) { free(v); }

struct timespec *li_allocTimespec() {
  return (struct timespec *)calloc(1, sizeof(struct timespec));
}

void *li_freeTimespec(struct timespec *v) { free(v); }

struct timespec *li_atime(struct stat *v) { return &(v->st_atim); }

struct timespec *li_ctime(struct stat *v) { return &(v->st_ctim); }

struct timespec *li_mtime(struct stat *v) { return &(v->st_mtim); }
