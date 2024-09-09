// Copyright 2024 Stefan Höck
//
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void *print_flag(const char *name, int value) {
  printf("\npublic export\n");
  printf("%s : WaitFlags\n", name);
  printf("%s = %d\n", name, value);
}

void *main() {
  print_flag("WUNTRACED", WUNTRACED);
  print_flag("WCONTINUED", WCONTINUED);
  print_flag("WNOHANG", WNOHANG);

  exit(0);
}
