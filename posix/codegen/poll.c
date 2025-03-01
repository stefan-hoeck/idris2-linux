// Copyright 2025 Stefan Höck
//
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <poll.h>

void *print_event(const char *name, unsigned int value) {
  printf("\npublic export\n");
  printf("%s : PollEvent\n", name);
  printf("%s = %u\n", name, value);
}

void *main() {
  print_event("POLLIN",    POLLIN);
  print_event("POLLOUT",   POLLOUT);
  print_event("POLLPRI",   POLLPRI);
  print_event("POLLERR",   POLLERR);
  print_event("POLLHUP",   POLLHUP);

  printf("\npublic export %%inline\n");
  printf("pollfd_size : Bits32\n");
  printf("pollfd_size = %zd\n", sizeof(struct pollfd));

  exit(0);
}

