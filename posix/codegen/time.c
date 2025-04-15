// Copyright 2024 Stefan Höck
//
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <time.h>

int main() {
  printf("\npublic export %%inline\n");
  printf("timespec_size : Bits32\n");
  printf("timespec_size = %zd\n", sizeof(struct timespec));

  printf("\npublic export %%inline\n");
  printf("tm_size : Bits32\n");
  printf("tm_size = %zd\n", sizeof(struct tm));

  exit(0);
}
