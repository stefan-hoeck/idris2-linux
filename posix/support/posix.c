// Copyright 2024 Stefan Höck

#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/statvfs.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

////////////////////////////////////////////////////////////////////////////////
// Error handling
////////////////////////////////////////////////////////////////////////////////

#define CHECKRES                                                               \
  if (res == -1) {                                                             \
    return -errno;                                                             \
  } else {                                                                     \
    return res;                                                                \
  }

uint32_t li_errno() { return errno; }

////////////////////////////////////////////////////////////////////////////////
// Files
////////////////////////////////////////////////////////////////////////////////

int li_open(const char *name, uint32_t flags, mode_t mode) {
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

ssize_t li_readlink(const char *pth, char *buf, size_t bytes) {
  int res = readlink(pth, buf, bytes);
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

int li_set_flags(int fd, uint32_t flags) {
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

int li_stat(const char *pth, struct stat *m) {
  int res = stat(pth, m);
  CHECKRES
}

int li_link(const char *pth, const char *lnk) {
  int res = link(pth, lnk);
  CHECKRES
}

int li_symlink(const char *pth, const char *lnk) {
  int res = symlink(pth, lnk);
  CHECKRES
}

int li_rename(const char *pth, const char *lnk) {
  int res = rename(pth, lnk);
  CHECKRES
}

int li_unlink(const char *pth) {
  int res = unlink(pth);
  CHECKRES
}

int li_remove(const char *pth) {
  int res = remove(pth);
  CHECKRES
}

////////////////////////////////////////////////////////////////////////////////
// Pipes
////////////////////////////////////////////////////////////////////////////////

int li_pipe(int fs[2]) {
  int res = pipe(fs);
  CHECKRES
}

int li_mkfifo(const char *pth, mode_t mode) {
  int res = mkfifo(pth, mode);
  CHECKRES
}

////////////////////////////////////////////////////////////////////////////////
// Directories
////////////////////////////////////////////////////////////////////////////////

int li_mkdir(const char *pth, mode_t mode) {
  int res = mkdir(pth, mode);
  CHECKRES
}

int li_rmdir(const char *pth) {
  int res = rmdir(pth);
  CHECKRES
}

typedef struct {
  DIR *dirptr;
} DirInfo;

DirInfo *calloc_dir() { return (DirInfo *)calloc(1, sizeof(DirInfo)); }

int li_opendir(const char *pth, DirInfo *di) {
  DIR *res = opendir(pth);
  if (res == NULL) {
    free(di);
    return -errno;
  } else {
    di->dirptr = res;
    return 0;
  }
}

int li_fdopendir(int fd, DirInfo *di) {
  DIR *res = fdopendir(fd);
  if (res == NULL) {
    free(di);
    return -errno;
  } else {
    di->dirptr = res;
    return 0;
  }
}

int li_closedir(DirInfo *di) {
  int res = closedir(di->dirptr);
  free(di);
  CHECKRES
}

void li_rewinddir(DirInfo *di) { rewinddir(di->dirptr); }

ssize_t li_readdir(DirInfo *di, char *buf) {
  errno = 0;
  struct dirent *res = readdir(di->dirptr);
  if (res == NULL) {
    return -errno;
  } else {
    strcpy(buf, res->d_name);
    return strlen(res->d_name);
  }
}

ssize_t li_getcwd(char *buf, size_t len) {
  errno = 0;
  char *res = getcwd(buf, len);
  if (res == NULL) {
    return -errno;
  } else {
    return strlen(buf);
  }
}

int li_chdir(const char *buf) {
  int res = chdir(buf);
  CHECKRES
}

int li_chroot(const char *buf) {
  int res = chroot(buf);
  CHECKRES
}

////////////////////////////////////////////////////////////////////////////////
// Processes
////////////////////////////////////////////////////////////////////////////////

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

pid_t li_fork() {
  pid_t res = fork();
  CHECKRES
}

pid_t li_wait(int *status) {
  pid_t res = wait(status);
  CHECKRES
}

pid_t li_waitpid(pid_t chld, int *status, uint32_t flags) {
  pid_t res = waitpid(chld, status, flags);
  CHECKRES
}

int li_waitid(idtype_t tpe, id_t id, siginfo_t *info, uint32_t options) {
  int res = waitid(tpe, id, info, options);
  CHECKRES
}

int li_execve(const char *pth, char *const args[], char *const env[]) {
  int res = execve(pth, args, env);
  CHECKRES
}

int li_execvp(const char *pth, char *const args[]) {
  int res = execvp(pth, args);
  CHECKRES
}

int li_execv(const char *pth, char *const args[]) {
  int res = execv(pth, args);
  CHECKRES
}

int li_system(const char *cmd) {
  int res = system(cmd);
  CHECKRES
}

uint8_t li_wifexited(int status) { return WIFEXITED(status); }

uint8_t li_wexitstatus(int status) { return WEXITSTATUS(status); }

uint8_t li_wifsignaled(int status) { return WIFSIGNALED(status); }

uint32_t li_wtermsig(int status) { return WTERMSIG(status); }

uint8_t li_wcoredump(int status) { return WCOREDUMP(status); }

uint8_t li_wifstopped(int status) { return WIFSTOPPED(status); }

uint32_t li_wstopsig(int status) { return WSTOPSIG(status); }

uint8_t li_wifcontinued(int status) { return WIFCONTINUED(status); }

////////////////////////////////////////////////////////////////////////////////
// Pthreads
////////////////////////////////////////////////////////////////////////////////

uint32_t li_pthread_join(pthread_t id) { return pthread_join(id, NULL); }

uint32_t li_pthread_mutex_init(pthread_mutex_t *m, uint8_t type) {
  pthread_mutexattr_t attr;
  int res;

  res = pthread_mutexattr_init(&attr);
  if (res > 0) {
    return res;
  }

  res = pthread_mutexattr_settype(&attr, type);
  if (res > 0) {
    return res;
  }

  res = pthread_mutex_init(m, &attr);

  pthread_mutexattr_destroy(&attr);

  return res;
}

void li_pthread_mutex_destroy(pthread_mutex_t *m) {
  pthread_mutex_destroy(m);
  free(m);
}

uint32_t li_pthread_cond_init(pthread_cond_t *c) {
  return pthread_cond_init(c, NULL);
}

void li_pthread_cond_destroy(pthread_cond_t *m) {
  pthread_cond_destroy(m);
  free(m);
}

uint8_t li_pthread_setcanceltype(uint8_t s) {
  int res;
  pthread_setcanceltype(s, &res);
  return res;
}

uint8_t li_pthread_setcancelstate(uint8_t s) {
  int res;
  pthread_setcancelstate(s, &res);
  return res;
}

void li_pthread_sigmask1(int how, sigset_t *set) {
  pthread_sigmask(how, set, NULL);
}

sigset_t *li_pthread_sigmask(int how, sigset_t *set) {
  sigset_t *old = malloc(sizeof(sigset_t));
  pthread_sigmask(how, set, old);
  return old;
}

sigset_t *li_pthread_siggetmask() { return li_pthread_sigmask(0, NULL); }

////////////////////////////////////////////////////////////////////////////////
// Signals
////////////////////////////////////////////////////////////////////////////////

int li_kill(pid_t p, int sig) {
  int res = kill(p, sig);
  CHECKRES
}

#ifndef __APPLE__
int li_sigqueue(pid_t p, int sig, int word) {
  union sigval u = {.sival_int = word};
  int res = sigqueue(p, sig, u);
  CHECKRES
}
#endif

sigset_t *li_emptysigset() {
  sigset_t *set = malloc(sizeof(sigset_t));
  sigemptyset(set);
  return set;
}

sigset_t *li_fullsigset() {
  sigset_t *set = malloc(sizeof(sigset_t));
  sigfillset(set);
  return set;
}

void li_sigprocmask1(int how, sigset_t *set) { sigprocmask(how, set, NULL); }

sigset_t *li_sigprocmask(int how, sigset_t *set) {
  sigset_t *old = malloc(sizeof(sigset_t));
  sigprocmask(how, set, old);
  return old;
}

sigset_t *li_sigpending() {
  sigset_t *set = malloc(sizeof(sigset_t));
  sigpending(set);
  return set;
}

sigset_t *li_siggetprocmask() { return li_sigprocmask(0, NULL); }

int li_pause() {
  int res = pause();
  CHECKRES
}

int li_sigsuspend(sigset_t *set) {
  int res = sigsuspend(set);
  CHECKRES
}

#ifndef __APPLE__
int li_sigwaitinfo(sigset_t *set, siginfo_t *info) {
  int res = sigwaitinfo(set, info);
  CHECKRES
}

int li_sigwait(sigset_t *set) {
  int sig;
  int res = sigwait(set, &sig);
  if (res < 0) {
    return -errno;
  } else {
    return sig;
  }
}

int li_sigtimedwait(sigset_t *set, siginfo_t *info, time_t sec, uint64_t nsec) {
  struct timespec ts;
  ts.tv_sec = sec;
  ts.tv_nsec = nsec;

  int res = sigtimedwait(set, info, &ts);
  CHECKRES
}
#endif

int get_siginfo_t_si_signo(siginfo_t *i) { return i->si_signo; }

int get_siginfo_t_si_code(siginfo_t *i) { return i->si_code; }

pid_t get_siginfo_t_si_pid(siginfo_t *i) { return i->si_pid; }

uid_t get_siginfo_t_si_uid(siginfo_t *i) { return i->si_uid; }

int get_siginfo_t_si_status(siginfo_t *i) { return i->si_status; }

int get_siginfo_t_si_value(siginfo_t *i) { return (i->si_value).sival_int; }

////////////////////////////////////////////////////////////////////////////////
// Timers
////////////////////////////////////////////////////////////////////////////////

struct timeval *li_timeval(time_t sec, suseconds_t usec) {
  struct timeval *res = malloc(sizeof(struct timeval));
  res->tv_sec = sec;
  res->tv_usec = usec;
  return res;
}

struct itimerval *li_itimerval(time_t int_sec, suseconds_t int_usec, time_t sec,
                               suseconds_t usec) {
  struct itimerval *res = malloc(sizeof(struct itimerval));
  res->it_value.tv_sec = sec;
  res->it_value.tv_usec = usec;
  res->it_interval.tv_sec = int_sec;
  res->it_interval.tv_usec = int_usec;
  return res;
}

#ifndef __APPLE__
struct itimerspec *li_itimerspec(time_t int_sec, int64_t int_nsec, time_t sec,
                                 int64_t nsec) {
  struct itimerspec *res = malloc(sizeof(struct itimerspec));
  res->it_value.tv_sec = sec;
  res->it_value.tv_nsec = nsec;
  res->it_interval.tv_sec = int_sec;
  res->it_interval.tv_nsec = int_nsec;
  return res;
}
#endif

int li_setitimer(int which, const struct itimerval *new,
                 struct itimerval *old) {
  int res = setitimer(which, new, old);
  CHECKRES
}

int li_setitimer1(int which, time_t int_sec, suseconds_t int_usec, time_t sec,
                  suseconds_t usec) {
  struct itimerval it;
  it.it_value.tv_sec = sec;
  it.it_value.tv_usec = usec;
  it.it_interval.tv_sec = int_sec;
  it.it_interval.tv_usec = int_usec;
  return li_setitimer(which, &it, NULL);
}

int li_nanosleep(const struct timespec *req, struct timespec *rem) {
  int res = nanosleep(req, rem);
  CHECKRES
}

int li_nanosleep1(time_t sec, uint32_t nsec) {
  struct timespec ts;
  ts.tv_sec = sec;
  ts.tv_nsec = nsec;
  return li_nanosleep(&ts, NULL);
}

int li_clock_gettime(clockid_t id, struct timespec *ref) {
  int res = clock_gettime(id, ref);
  CHECKRES
}

int li_clock_getres(clockid_t id, struct timespec *ref) {
  int res = clock_getres(id, ref);
  CHECKRES
}

#ifndef __APPLE__
uint32_t li_clock_nanosleep(clockid_t id, struct timespec *ref,
                            struct timespec *rem) {
  return clock_nanosleep(id, 0, ref, rem);
}

uint32_t li_clock_nanosleep_abs(clockid_t id, struct timespec *ref) {
  return clock_nanosleep(id, TIMER_ABSTIME, ref, NULL);
}
#endif

////////////////////////////////////////////////////////////////////////////////
// Structs
////////////////////////////////////////////////////////////////////////////////

// timespec

time_t get_tv_sec(struct timespec *v) { return v->tv_sec; }

int64_t get_tv_nsec(struct timespec *v) { return v->tv_nsec; }

void set_tv_sec(struct timespec *v, time_t val) { v->tv_sec = val; }

void set_tv_nsec(struct timespec *v, int64_t val) { v->tv_nsec = val; }

// statvs

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

#ifndef __APPLE__
struct timespec *get_stat_st_atim(struct stat *v) { return &(v->st_atim); }

struct timespec *get_stat_st_mtim(struct stat *v) { return &(v->st_mtim); }

struct timespec *get_stat_st_ctim(struct stat *v) { return &(v->st_ctim); }
#endif

// timeval

time_t get_timeval_tv_sec(struct timeval *v) { return v->tv_sec; }

suseconds_t get_timeval_tv_usec(struct timeval *v) { return v->tv_usec; }

void set_timeval_tv_sec(struct timeval *v, time_t val) { v->tv_sec = val; }

void set_timeval_tv_usec(struct timeval *v, suseconds_t val) {
  v->tv_usec = val;
}

// itimerval

struct timeval *get_itimerval_it_interval(struct itimerval *v) {
  return &v->it_interval;
}

struct timeval *get_itimerval_it_value(struct itimerval *v) {
  return &v->it_value;
}

void set_itimerval_it_interval(struct itimerval *v, struct timeval *val) {
  v->it_interval = *val;
}

void set_itimerval_it_value(struct itimerval *v, struct timeval *val) {
  v->it_value = *val;
}

// itimerspec

#ifndef __APPLE__
struct timespec *get_itimerspec_it_interval(struct itimerspec *v) {
  return &v->it_interval;
}

struct timespec *get_itimerspec_it_value(struct itimerspec *v) {
  return &v->it_value;
}

void set_itimerspec_it_interval(struct itimerspec *v, struct timespec *val) {
  v->it_interval = *val;
}

void set_itimerspec_it_value(struct itimerspec *v, struct timespec *val) {
  v->it_value = *val;
}
#endif
