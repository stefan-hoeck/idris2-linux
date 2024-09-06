// Copyright 2024 Stefan Höck
//
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <time.h>

void *print_which(const char *name, int value) {
  printf("whichCode %s = %d\n", name, value);
}

void *main() {
  printf("\npublic export\n");
  printf("whichCode : Which -> Bits8\n");
  print_which("ITIMER_REAL", ITIMER_REAL);
  print_which("ITIMER_VIRTUAL", ITIMER_VIRTUAL);
  print_which("ITIMER_PROF", ITIMER_PROF);

  printf("\npublic export %%inline\n");
  printf("timeval_size : SizeT\n");
  printf("timeval_size = %zd\n", sizeof(struct timeval));

  printf("\npublic export %%inline\n");
  printf("itimerval_size : SizeT\n");
  printf("itimerval_size = %zd\n", sizeof(struct itimerval));

  printf("\npublic export %%inline\n");
  printf("CLOCKS_PER_SEC : ClockT\n");
  printf("CLOCKS_PER_SEC = %lld\n", CLOCKS_PER_SEC);

  exit(0);
}
