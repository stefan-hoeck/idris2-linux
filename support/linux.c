// Copyright 2024 Stefan Höck

#include <errno.h>
#include <stdint.h>
#include <stdio.h>

uint32_t li_errno() { return errno; }
