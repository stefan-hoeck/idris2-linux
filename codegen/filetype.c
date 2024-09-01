// Copyright 2024 Stefan Höck
//
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/stat.h>

void *print_case(const char *name, int value) {
  printf("    %d => %s\n", value, name);
}

void *main() {
  printf("fromMode m =\n");
  printf("  case m .&. %d of\n", S_IFMT);
  print_case("Regular", S_IFREG);
  print_case("Directory", S_IFDIR);
  print_case("CharDevice", S_IFCHR);
  print_case("BlockDevice", S_IFBLK);
  print_case("Pipe", S_IFIFO);
  print_case("Socket", S_IFSOCK);
  print_case("Link", S_IFLNK);
  printf("    _ => Other\n");

  exit(0);
}
