// Copyright 2024 Stefan Höck
//
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/inotify.h>

void *print_mask(const char *name, int value) {
  printf("\npublic export\n");
  printf("%s : InotifyMask\n", name);
  printf("%s = %d\n", name, value);
}

void *print_flag(const char *name, int value) {
  printf("\npublic export\n");
  printf("%s : InotifyFlags\n", name);
  printf("%s = %d\n", name, value);
}

void *main() {
  print_flag("IN_NONBLOCK", IN_NONBLOCK);
  print_flag("IN_CLOEXEC", IN_CLOEXEC);

  print_mask("IN_ACCESS", IN_ACCESS);
  print_mask("IN_ATTRIB", IN_ATTRIB);
  print_mask("IN_CLOSE_WRITE", IN_CLOSE_WRITE);
  print_mask("IN_CLOSE_NOWRITE", IN_CLOSE_NOWRITE);
  print_mask("IN_CREATE", IN_CREATE);
  print_mask("IN_DELETE", IN_DELETE);
  print_mask("IN_DELETE_SELF", IN_DELETE_SELF);
  print_mask("IN_MODIFY", IN_MODIFY);
  print_mask("IN_MOVE_SELF", IN_MOVE_SELF);
  print_mask("IN_MOVED_FROM", IN_MOVED_FROM);
  print_mask("IN_MOVED_TO", IN_MOVED_TO);
  print_mask("IN_OPEN", IN_OPEN);
  print_mask("IN_ALL_EVENTS", IN_ALL_EVENTS);
  print_mask("IN_MOVE", IN_MOVE);
  print_mask("IN_CLOSE", IN_CLOSE);
  print_mask("IN_DONT_FOLLOW", IN_DONT_FOLLOW);
  print_mask("IN_EXCL_UNLINK", IN_EXCL_UNLINK);
  print_mask("IN_MASK_ADD", IN_MASK_ADD);
  print_mask("IN_ONESHOT", IN_ONESHOT);
  print_mask("IN_ONLYDIR", IN_ONLYDIR);
  print_mask("IN_MASK_CREATE", IN_MASK_CREATE);
  print_mask("IN_IGNORED", IN_IGNORED);
  print_mask("IN_ISDIR", IN_ISDIR);
  print_mask("IN_Q_OVERFLOW", IN_Q_OVERFLOW);
  print_mask("IN_UNMOUNT", IN_UNMOUNT);

  exit(0);
}
