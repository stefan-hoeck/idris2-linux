// Copyright 2024 Stefan Höck
//
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>

void print_how(const char *name, int value) {
  printf("howCode %s = %d\n", name, value);
}

void print_signal(const char *name, int value) {
  printf("\npublic export %%inline\n");
  printf("%s : Signal\n", name);
  printf("%s = %d\n", name, value);
}

void print_pair(const char *name) {
  printf("    , (%s, \"%s\")\n", name, name);
}

int main() {
  printf("\npublic export\n");
  printf("howCode : How -> Bits8\n");
  print_how("SIG_BLOCK  ", SIG_BLOCK);
  print_how("SIG_UNBLOCK", SIG_UNBLOCK);
  print_how("SIG_SETMASK", SIG_SETMASK);

#ifdef __GLIBC__
  printf("\npublic export\n");
  printf("SIGRTMIN : Signal\n");
  printf("SIGRTMIN = %d\n", SIGRTMIN);

  printf("\npublic export\n");
  printf("SIGRTMAX : Signal\n");
  printf("SIGRTMAX = %d\n", SIGRTMAX);
#else
  printf("\npublic export\n");
  printf("SIGRTMIN : Signal\n");
  printf("SIGRTMIN = 0\n");

  printf("\npublic export\n");
  printf("SIGRTMAX : Signal\n");
  printf("SIGRTMAX = 0\n");
#endif

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
  print_signal("SIGSYS", SIGSYS);
#ifdef __GLIBC__
  print_signal("SIGPOLL", SIGPOLL);
#endif

  printf("\nexport\n");
  printf("sigName : SortedMap Signal String\n");
  printf("sigName =\n");
  printf("  SortedMap.fromList\n");
  printf("    [ (SIGHUP, \"SIGHUP\")\n");
  print_pair("SIGINT");
  print_pair("SIGQUIT");
  print_pair("SIGILL");
  print_pair("SIGTRAP");
  print_pair("SIGABRT");
  print_pair("SIGBUS");
  print_pair("SIGFPE");
  print_pair("SIGKILL");
  print_pair("SIGUSR1");
  print_pair("SIGSEGV");
  print_pair("SIGUSR2");
  print_pair("SIGPIPE");
  print_pair("SIGALRM");
  print_pair("SIGTERM");
  print_pair("SIGCHLD");
  print_pair("SIGCONT");
  print_pair("SIGSTOP");
  print_pair("SIGTSTP");
  print_pair("SIGTTIN");
  print_pair("SIGTTOU");
  print_pair("SIGURG");
  print_pair("SIGXCPU");
  print_pair("SIGXFSZ");
  print_pair("SIGVTALRM");
  print_pair("SIGPROF");
  print_pair("SIGSYS");
#ifdef __GLIBC__
  print_pair("SIGPOLL");
#endif
  printf("    ]\n");

  printf("\npublic export %%inline\n");
  printf("siginfo_t_size : Bits32\n");
  printf("siginfo_t_size = %zd\n", sizeof(siginfo_t));

  exit(0);
}
