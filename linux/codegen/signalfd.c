// Copyright 2024 Stefan Höck
//
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/signalfd.h>

void *print_flag(const char *name, int value) {
  printf("\npublic export\n");
  printf("%s : SignalfdFlags\n", name);
  printf("%s = %d\n", name, value);
}

void *main() {
  print_flag("SFD_CLOEXEC", SFD_CLOEXEC);
  print_flag("SFD_NONBLOCK", SFD_NONBLOCK);

  printf("\npublic export\n");
  printf("signalfd_siginfo_size : Bits32\n");
  printf("signalfd_siginfo_size = %zd\n", sizeof(struct signalfd_siginfo));

  exit(0);
}
