// Copyright 2024 Stefan Höck
//
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/timerfd.h>

void *print_flag(const char *name, int value) {
  printf("\npublic export\n");
  printf("%s : TimerfdFlags\n", name);
  printf("%s = %d\n", name, value);
}

void *main() {
  print_flag("TFD_CLOEXEC", TFD_CLOEXEC);
  print_flag("TFD_NONBLOCK", TFD_NONBLOCK);

  printf("\npublic export\n");
  printf("TFD_TIMER_ABSTIME : Bits32\n");
  printf("TFD_TIMER_ABSTIME = %d\n", TFD_TIMER_ABSTIME);
  exit(0);
}
