// Copyright 2024 Stefan Höck

#include <errno.h>
#include <stdio.h>
#include <stdint.h>

uint32_t li_errno() {
    return errno;
}
