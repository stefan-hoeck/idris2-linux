// Copyright 2024 Stefan Höck
//
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void print_flag(const char *name, int value) {
  printf("\npublic export\n");
  printf("%s : Flags\n", name);
  printf("%s = %d\n", name, value);
}

void print_mode(const char *name, int value) {
  printf("\npublic export\n");
  printf("%s : Mode\n", name);
  printf("%s = %d\n", name, value);
}

int main() {
  print_flag("O_RDONLY", O_RDONLY);
  print_flag("O_WRONLY", O_WRONLY);
  print_flag("O_RDWR", O_RDWR);
  print_flag("O_CLOEXEC", O_CLOEXEC);
  print_flag("O_CREAT", O_CREAT);
  print_flag("O_DIRECTORY", O_DIRECTORY);
  print_flag("O_EXCL", O_EXCL);
  print_flag("O_NOCTTY", O_NOCTTY);
  print_flag("O_NOFOLLOW", O_NOFOLLOW);
  print_flag("O_TRUNC", O_TRUNC);
  print_flag("O_APPEND", O_APPEND);
  print_flag("O_ASYNC", O_ASYNC);
  print_flag("O_DSYNC", O_DSYNC);
  print_flag("O_NONBLOCK", O_NONBLOCK);
  print_flag("O_SYNC", O_SYNC);

  print_mode("S_IRWXU", S_IRWXU);
  print_mode("S_IRUSR", S_IRUSR);
  print_mode("S_IWUSR", S_IWUSR);
  print_mode("S_IXUSR", S_IXUSR);
  print_mode("S_IRWXG", S_IRWXG);
  print_mode("S_IRGRP", S_IRGRP);
  print_mode("S_IWGRP", S_IWGRP);
  print_mode("S_IXGRP", S_IXGRP);
  print_mode("S_IRWXO", S_IRWXO);
  print_mode("S_IROTH", S_IROTH);
  print_mode("S_IWOTH", S_IWOTH);
  print_mode("S_IXOTH", S_IXOTH);

#ifdef __GLIBC__
  print_mode("S_ISUID", S_ISUID);
  print_mode("S_ISGID", S_ISGID);
  print_mode("S_ISVTX", S_ISVTX);
#endif

  exit(0);
}
