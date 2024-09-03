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
all: error_gen flags_gen whence_gen limits_gen filetype_gen

error_gen: error.c
	$(CC) $(LDFLAGS) -o error_gen error.c

flags_gen: flags.c
	$(CC) $(LDFLAGS) -o flags_gen flags.c

whence_gen: whence.c
	$(CC) $(LDFLAGS) -o whence_gen whence.c

limits_gen: limits.c
	$(CC) $(LDFLAGS) -o limits_gen limits.c

filetype_gen: filetype.c
	$(CC) $(LDFLAGS) -o filetype_gen filetype.c
