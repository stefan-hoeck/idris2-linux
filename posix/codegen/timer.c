// Copyright 2024 Stefan Höck
//
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <time.h>

void print_which(const char *name, int value) {
  printf("whichCode %s = %d\n", name, value);
}

void print_clock(const char *name, int value) {
  printf("clockCode %s = %d\n", name, value);
}

int main() {
  printf("\npublic export\n");
  printf("whichCode : Which -> Bits8\n");
  print_which("ITIMER_REAL", ITIMER_REAL);
  print_which("ITIMER_VIRTUAL", ITIMER_VIRTUAL);
  print_which("ITIMER_PROF", ITIMER_PROF);

  printf("\npublic export\n");
  printf("clockCode : ClockId -> Bits8\n");
  print_clock("CLOCK_REALTIME", CLOCK_REALTIME);
  print_clock("CLOCK_MONOTONIC", CLOCK_MONOTONIC);
  print_clock("CLOCK_PROCESS_CPUTIME_ID", CLOCK_PROCESS_CPUTIME_ID);
  print_clock("CLOCK_THREAD_CPUTIME_ID", CLOCK_THREAD_CPUTIME_ID);

  printf("\npublic export %%inline\n");
  printf("timeval_size : Bits32\n");
  printf("timeval_size = %zd\n", sizeof(struct timeval));

  printf("\npublic export %%inline\n");
  printf("itimerval_size : Bits32\n");
  printf("itimerval_size = %zd\n", sizeof(struct itimerval));

  printf("\npublic export %%inline\n");
  printf("itimerspec_size : Bits32\n");
#ifdef __APPLE__
  // This isn't intended to be functional on darwin, just support compilation
  // of the Idris counterpart.
  printf("itimerspec_size = 0\n");
#else
  printf("itimerspec_size = %zd\n", sizeof(struct itimerspec));
#endif

  printf("\npublic export %%inline\n");
  printf("CLOCKS_PER_SEC : ClockT\n");
  printf("CLOCKS_PER_SEC = %lld\n", (long long)CLOCKS_PER_SEC);

  exit(0);
}
