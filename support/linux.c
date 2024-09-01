// Copyright 2024 Stefan Höck

#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>
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

int li_stat(const char *pth, struct stat *m) {
  int res = stat(pth, m);
  CHECKRES
}

// timespec

time_t get_timespec_tv_sec(struct timespec *v) { return v->tv_sec; }

int64_t get_timespec_tv_nsec(struct timespec *v) { return v->tv_nsec; }

void set_timespec_tv_sec(struct timespec *v, time_t val) { v->tv_sec = val; }

void set_timespec_tv_nsec(struct timespec *v, int64_t val) { v->tv_nsec = val; }

// statvs

struct statvfs *calloc_statvfs() {
  return (struct statvfs *)calloc(1, sizeof(struct statvfs));
}

uint64_t get_statvfs_f_bsize(struct statvfs *v) { return v->f_bsize; }

uint64_t get_statvfs_f_frsize(struct statvfs *v) { return v->f_frsize; }

fsblkcnt_t get_statvfs_f_blocks(struct statvfs *v) { return v->f_blocks; }

fsblkcnt_t get_statvfs_f_bfree(struct statvfs *v) { return v->f_bfree; }

fsblkcnt_t get_statvfs_f_bavail(struct statvfs *v) { return v->f_bavail; }

fsfilcnt_t get_statvfs_f_files(struct statvfs *v) { return v->f_files; }

fsfilcnt_t get_statvfs_f_ffree(struct statvfs *v) { return v->f_ffree; }

fsfilcnt_t get_statvfs_f_favail(struct statvfs *v) { return v->f_favail; }

uint64_t get_statvfs_f_fsid(struct statvfs *v) { return v->f_fsid; }

uint64_t get_statvfs_f_flag(struct statvfs *v) { return v->f_flag; }

uint64_t get_statvfs_f_namemax(struct statvfs *v) { return v->f_namemax; }

// stat

struct stat *calloc_stat() {
  return (struct stat *)calloc(1, sizeof(struct stat));
}

dev_t get_stat_st_dev(struct stat *v) { return v->st_dev; }

ino_t get_stat_st_ino(struct stat *v) { return v->st_ino; }

mode_t get_stat_st_mode(struct stat *v) { return v->st_mode; }

nlink_t get_stat_st_nlink(struct stat *v) { return v->st_nlink; }

uid_t get_stat_st_uid(struct stat *v) { return v->st_uid; }

gid_t get_stat_st_gid(struct stat *v) { return v->st_gid; }

dev_t get_stat_st_rdev(struct stat *v) { return v->st_rdev; }

off_t get_stat_st_size(struct stat *v) { return v->st_size; }

size_t get_stat_st_blksize(struct stat *v) { return v->st_blksize; }

blkcnt_t get_stat_st_blocks(struct stat *v) { return v->st_blocks; }

struct timespec *get_stat_st_atim(struct stat *v) { return &(v->st_atim); }

struct timespec *get_stat_st_mtim(struct stat *v) { return &(v->st_mtim); }

struct timespec *get_stat_st_ctim(struct stat *v) { return &(v->st_ctim); }
