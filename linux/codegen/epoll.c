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
  printf("\npublic export\n");
  printf("opCode : EpollOp -> Bits32\n");
  printf("opCode Add = %d\n", EPOLL_CTL_ADD);
  printf("opCode Del = %d\n", EPOLL_CTL_DEL);
  printf("opCode Mod = %d\n", EPOLL_CTL_MOD);

  print_event("EPOLLIN",    EPOLLIN);
  print_event("EPOLLOUT",   EPOLLOUT);
  print_event("EPOLLRDHUP", EPOLLRDHUP);
  print_event("EPOLLPRI",   EPOLLPRI);
  print_event("EPOLLERR",   EPOLLERR);
  print_event("EPOLLHUP",   EPOLLHUP);
  print_event("EPOLLET", EPOLLET);
  print_event("EPOLLONESHOT", EPOLLONESHOT);
  print_event("EPOLLWAKEUP", EPOLLWAKEUP);
  print_event("EPOLLEXCLUSIVE", EPOLLEXCLUSIVE);

  print_flag("EPOLL_CLOEXEC", EPOLL_CLOEXEC);

  printf("\npublic export %%inline\n");
  printf("epoll_event_size : Bits32\n");
  printf("epoll_event_size = %zd\n", sizeof(struct epoll_event));

  exit(0);
}
