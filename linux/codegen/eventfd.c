// Copyright 2024 Stefan Höck
//
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/eventfd.h>

void *print_flag(const char *name, int value) {
  printf("\npublic export\n");
  printf("%s : EventfdFlags\n", name);
  printf("%s = %d\n", name, value);
}

void *main() {
  print_flag("EFD_CLOEXEC", EFD_CLOEXEC);
  print_flag("EFD_NONBLOCK", EFD_NONBLOCK);
  print_flag("EFD_SEMAPHORE", EFD_SEMAPHORE);

  exit(0);
}
