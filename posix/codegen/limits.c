// Copyright 2024 Stefan Höck
//
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

void print_limit(const char *name, int value) {
  printf("\npublic export\n");
  printf("%s : Bits32\n", name);
  printf("%s = %d\n", name, value);
}

int main() {
  print_limit("SC_ARG_MAX", _SC_ARG_MAX);
  print_limit("SC_CHILD_MAX", _SC_CHILD_MAX);
  print_limit("SC_HOST_NAME_MAX", _SC_HOST_NAME_MAX);
  print_limit("SC_LOGIN_NAME_MAX", _SC_LOGIN_NAME_MAX);
  print_limit("SC_NGROUPS_MAX", _SC_NGROUPS_MAX);
  print_limit("SC_CLK_TCK", _SC_CLK_TCK);
  print_limit("SC_OPEN_MAX", _SC_OPEN_MAX);
  print_limit("SC_PAGESIZE", _SC_PAGESIZE);
  print_limit("SC_PAGE_SIZE", _SC_PAGE_SIZE);
  print_limit("SC_RE_DUP_MAX", _SC_RE_DUP_MAX);
  print_limit("SC_STREAM_MAX", _SC_STREAM_MAX);
  print_limit("SC_SYMLOOP_MAX", _SC_SYMLOOP_MAX);
  print_limit("SC_TTY_NAME_MAX", _SC_TTY_NAME_MAX);
  print_limit("SC_TZNAME_MAX", _SC_TZNAME_MAX);
  print_limit("SC_VERSION", _SC_VERSION);
  print_limit("SC_BC_BASE_MAX", _SC_BC_BASE_MAX);
  print_limit("SC_BC_DIM_MAX", _SC_BC_DIM_MAX);
  print_limit("SC_BC_SCALE_MAX", _SC_BC_SCALE_MAX);
  print_limit("SC_BC_STRING_MAX", _SC_BC_STRING_MAX);
  print_limit("SC_COLL_WEIGHTS_MAX", _SC_COLL_WEIGHTS_MAX);
  print_limit("SC_EXPR_NEST_MAX", _SC_EXPR_NEST_MAX);
  print_limit("SC_RTSIG_MAX", _SC_RTSIG_MAX);
  print_limit("SC_SIGQUEUE_MAX", _SC_SIGQUEUE_MAX);
  print_limit("SC_LINE_MAX", _SC_LINE_MAX);
  print_limit("SC_2_VERSION", _SC_2_VERSION);
  print_limit("SC_2_C_DEV", _SC_2_C_DEV);
  print_limit("SC_2_FORT_DEV", _SC_2_FORT_DEV);
  print_limit("SC_2_FORT_RUN", _SC_2_FORT_RUN);
  print_limit("SC_2_LOCALEDEF", _SC_2_LOCALEDEF);
  print_limit("SC_2_SW_DEV", _SC_2_SW_DEV);

  print_limit("PC_LINK_MAX", _PC_LINK_MAX);
  print_limit("PC_MAX_CANON", _PC_MAX_CANON);
  print_limit("PC_MAX_INPUT", _PC_MAX_INPUT);
  print_limit("PC_NAME_MAX", _PC_NAME_MAX);
  print_limit("PC_PATH_MAX", _PC_PATH_MAX);
  print_limit("PC_PIPE_BUF", _PC_PIPE_BUF);
  print_limit("PC_CHOWN_RESTRICTED", _PC_CHOWN_RESTRICTED);
  print_limit("PC_NO_TRUNC", _PC_NO_TRUNC);
  print_limit("PC_VDISABLE", _PC_VDISABLE);

  exit(0);
}
