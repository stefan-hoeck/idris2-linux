// Copyright 2024 Stefan Höck
//
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>

void *print_code(const char *name, int value) {
  printf("mutexCode %s = %d\n", name, value);
}

void *main() {
  printf("\npublic export\n");
  printf("mutexCode : MutexType -> Bits8\n");
  print_code("MUTEX_NORMAL", PTHREAD_MUTEX_NORMAL);
  print_code("MUTEX_RECURSIVE", PTHREAD_MUTEX_RECURSIVE);
  print_code("MUTEX_ERRORCHECK", PTHREAD_MUTEX_ERRORCHECK);

  printf("\npublic export %%inline\n");
  printf("pthread_t_size : Nat\n");
  printf("pthread_t_size = %zd\n", sizeof(pthread_t));

  printf("\npublic export %%inline\n");
  printf("mutex_t_size : Nat\n");
  printf("mutex_t_size = %zd\n", sizeof(pthread_mutex_t));

  printf("\npublic export %%inline\n");
  printf("cond_t_size : Nat\n");
  printf("cond_t_size = %zd\n", sizeof(pthread_cond_t));

  exit(0);
}
