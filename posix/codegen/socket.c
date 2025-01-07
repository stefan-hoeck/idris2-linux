// Copyright 2024 Stefan Höck
//
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>

void print_domain(const char *name, int value) {
  printf("domainCode %s = %d\n", name, value);
}

void print_type(const char *name, int value) {
  printf("\npublic export\n");
  printf("%s : SockType\n", name);
  printf("%s = %d\n", name, value);
}

int main() {
  printf("\npublic export\n");
  printf("domainCode : Domain -> Bits8\n");
  print_domain("AF_UNIX ", AF_UNIX);
  print_domain("AF_INET ", AF_INET);
  print_domain("AF_INET6", AF_INET6);

  print_type("SOCK_STREAM", SOCK_STREAM);
  print_type("SOCK_DGRAM", SOCK_DGRAM);
  print_type("SOCK_RAW", SOCK_RAW);
#ifdef __GLIBC__
  print_type("SOCK_NONBLOCK", SOCK_NONBLOCK);
  print_type("SOCK_CLOEXEC", SOCK_CLOEXEC);
#endif

  exit(0);
}
