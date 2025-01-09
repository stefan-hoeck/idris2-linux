// Copyright 2024 Stefan Höck
//
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <netinet/in.h>

void print_domain(const char *name, int value) {
  printf("domainCode %s = %d\n", name, value);
}

void print_type(const char *name, int value) {
  printf("\npublic export\n");
  printf("%s : SockType\n", name);
  printf("%s = %d\n", name, value);
}

void print_flag(const char *name, int value) {
  printf("\npublic export\n");
  printf("%s : SockFlags\n", name);
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

  print_flag("MSG_DONTWAIT", MSG_DONTWAIT);
  print_flag("MSG_OOB", MSG_OOB);
  print_flag("MSG_PEEK", MSG_PEEK);
  print_flag("MSG_WAITALL", MSG_WAITALL);
  print_flag("MSG_NOSIGNAL", MSG_NOSIGNAL);

  printf("\npublic export\n");
  printf("sockaddr_un_size : Bits32\n");
  printf("sockaddr_un_size = %zd\n", sizeof(struct sockaddr_un));

  printf("\npublic export\n");
  printf("sockaddr_in_size : Bits32\n");
  printf("sockaddr_in_size = %zd\n", sizeof(struct sockaddr_in));

  printf("\npublic export\n");
  printf("sockaddr_in6_size : Bits32\n");
  printf("sockaddr_in6_size = %zd\n", sizeof(struct sockaddr_in6));

  exit(0);
}
