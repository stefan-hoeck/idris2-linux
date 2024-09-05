// Copyright 2024 Stefan Höck
//
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>

void *print_how(const char *name, int value) {
  printf("howCode %s = %d\n", name, value);
}

void *print_flag(const char *name, long value) {
  printf("\npublic export\n");
  printf("%s : SignalFlags\n", name);
  printf("%s = %ld\n", name, value);
}

void *main() {
  printf("\npublic export\n");
  printf("howCode : How -> Bits8\n");
  print_how("SIG_BLOCK  ", SIG_BLOCK);
  print_how("SIG_UNBLOCK", SIG_UNBLOCK);
  print_how("SIG_SETMASK", SIG_SETMASK);

  print_flag("SA_NOCLDSTOP", SA_NOCLDSTOP);
  print_flag("SA_NOCLDWAIT", SA_NOCLDWAIT);
  print_flag("SA_NODEFER", SA_NODEFER);
  print_flag("SA_ONSTACK", SA_ONSTACK);
  print_flag("SA_RESETHAND", SA_RESETHAND);
  print_flag("SA_RESTART", SA_RESTART);
  print_flag("SA_SIGINFO", SA_SIGINFO);

  exit(0);
}
