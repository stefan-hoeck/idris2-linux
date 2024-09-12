// Copyright 2024 Stefan Höck
//
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>

void *print_flag(const char *name, int value) {
  printf("\npublic export\n");
  printf("%s : WaitFlags\n", name);
  printf("%s = %d\n", name, value);
}

void *print_idtype(const char *name, idtype_t tpe) {
  printf("idtypeCode %s = %d\n", name, tpe);
}

void *main() {
  print_flag("WUNTRACED", WUNTRACED);
  print_flag("WCONTINUED", WCONTINUED);
  print_flag("WNOHANG", WNOHANG);
  print_flag("WEXITED", WEXITED);
  print_flag("WSTOPPED", WSTOPPED);
  print_flag("WNOWAIT", WNOWAIT);

  printf("\npublic export\n");
  printf("idtypeCode : IdType -> Bits8\n");
  print_idtype("P_ALL", P_ALL);
  print_idtype("P_PID", P_PID);
  print_idtype("P_PGID", P_PGID);
  print_idtype("P_PIDFD", P_PIDFD);

  exit(0);
}
