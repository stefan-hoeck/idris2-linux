// Copyright 2024 Stefan Höck
//
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>

void *print_how(const char *name, int value) {
  printf("howCode %s = %d\n", name, value);
}

void *print_signal(const char *name, int value) {
  printf("\npublic export\n");
  printf("%s : Signal\n", name);
  printf("%s = %d\n", name, value);
}

void *main() {
  printf("\npublic export\n");
  printf("howCode : How -> Bits8\n");
  print_how("SIG_BLOCK  ", SIG_BLOCK);
  print_how("SIG_UNBLOCK", SIG_UNBLOCK);
  print_how("SIG_SETMASK", SIG_SETMASK);

  printf("\npublic export\n");
  printf("SIGRTMIN : Signal\n");
  printf("SIGRTMIN = %d\n", SIGRTMIN);

  printf("\npublic export\n");
  printf("SIGRTMAX : Signal\n");
  printf("SIGRTMAX = %d\n", SIGRTMAX);

  print_signal("SIGHUP", SIGHUP);
  print_signal("SIGINT", SIGINT);
  print_signal("SIGQUIT", SIGQUIT);
  print_signal("SIGILL", SIGILL);
  print_signal("SIGTRAP", SIGTRAP);
  print_signal("SIGABRT", SIGABRT);
  print_signal("SIGBUS", SIGBUS);
  print_signal("SIGFPE", SIGFPE);
  print_signal("SIGKILL", SIGKILL);
  print_signal("SIGUSR1", SIGUSR1);
  print_signal("SIGSEGV", SIGSEGV);
  print_signal("SIGUSR2", SIGUSR2);
  print_signal("SIGPIPE", SIGPIPE);
  print_signal("SIGALRM", SIGALRM);
  print_signal("SIGTERM", SIGTERM);
  print_signal("SIGCHLD", SIGCHLD);
  print_signal("SIGCONT", SIGCONT);
  print_signal("SIGSTOP", SIGSTOP);
  print_signal("SIGTSTP", SIGTSTP);
  print_signal("SIGTTIN", SIGTTIN);
  print_signal("SIGTTOU", SIGTTOU);
  print_signal("SIGURG", SIGURG);
  print_signal("SIGXCPU", SIGXCPU);
  print_signal("SIGXFSZ", SIGXFSZ);
  print_signal("SIGVTALRM", SIGVTALRM);
  print_signal("SIGPROF", SIGPROF);
  print_signal("SIGPOLL", SIGPOLL);
  print_signal("SIGSYS", SIGSYS);

  printf("\npublic export %%inline\n");
  printf("siginfo_t_size : SizeT\n");
  printf("siginfo_t_size = %zd\n", sizeof(siginfo_t));

  exit(0);
}
