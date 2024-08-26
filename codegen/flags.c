// Copyright 2024 Stefan Höck
//
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <sys/stat.h>

void *print_flag(const char *name, int value) {
    printf("\npublic export\n");
    printf("%s : Flags\n", name);
    printf("%s = %d\n", name, value);
}

void *main() {
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

  exit(0);
}
