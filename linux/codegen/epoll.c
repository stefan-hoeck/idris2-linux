// Copyright 2024 Stefan Höck
//
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/epoll.h>

void *print_event(const char *name, unsigned int value) {
  printf("\npublic export\n");
  printf("%s : Event\n", name);
  printf("%s = %u\n", name, value);
}

void *print_flag(const char *name, unsigned int value) {
  printf("\npublic export\n");
  printf("%s : EpollFlags\n", name);
  printf("%s = %u\n", name, value);
}

void *main() {
  print_event("EPOLLIN",    EPOLLIN);
  print_event("EPOLLOUT",   EPOLLOUT);
  print_event("EPOLLRDHUP", EPOLLRDHUP);
  print_event("EPOLLPRI",   EPOLLPRI);
  print_event("EPOLLERR",   EPOLLERR);
  print_event("EPOLLHUP",   EPOLLHUP);

  print_flag("EPOLLET", EPOLLET);
  print_flag("EPOLLONESHOT", EPOLLONESHOT);
  print_flag("EPOLLWAKEUP", EPOLLWAKEUP);
  print_flag("EPOLLEXCLUSIVE", EPOLLEXCLUSIVE);

  exit(0);
}
