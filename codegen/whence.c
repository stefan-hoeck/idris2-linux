// Copyright 2024 Stefan Höck
//
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void *print_whence(const char *name, int value) {
  printf("whenceCode %s = %d\n", name, value);
}

void *main() {
  print_whence("SEEK_SET", SEEK_SET);
  print_whence("SEEK_CUR", SEEK_CUR);
  print_whence("SEEK_END", SEEK_END);

  exit(0);
}

