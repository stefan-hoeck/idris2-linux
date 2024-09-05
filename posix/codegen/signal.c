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

void *main() {
  printf("\npublic export\n");
  printf("howCode : How -> Bits8\n");
  print_how("SIG_BLOCK  ", SIG_BLOCK);
  print_how("SIG_UNBLOCK", SIG_UNBLOCK);
  print_how("SIG_SETMASK", SIG_SETMASK);

  exit(0);
}
