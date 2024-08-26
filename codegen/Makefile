LDFLAGS =
CPPFLAGS =

CC_VERSION = $(shell $(CC) --version)

ifeq ($(findstring clang,$(CC_VERSION)),clang)
	DYLIB_WORKAROUND = cp "${INSTALLDIR}/${TARGET}" "${INSTALLDIR}/${TARGET}.dylib"
else
	DYLIB_WORKAROUND = cp "${INSTALLDIR}/${TARGET}" "${INSTALLDIR}/${TARGET}.so"
	LDFLAGS += -fuse-ld=gold
endif

.PHONY: all
all: error_gen flags_gen

error_gen: error.c
	$(CC) $(LDFLAGS) -o error_gen error.c

flags_gen: flags.c
	$(CC) $(LDFLAGS) -o flags_gen flags.c
