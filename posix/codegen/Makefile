LDFLAGS =
CPPFLAGS =

CC_VERSION = $(shell $(CC) --version)

ifeq ($(findstring clang,$(CC_VERSION)),clang)
	DYLIB_WORKAROUND = cp "${INSTALLDIR}/${TARGET}" "${INSTALLDIR}/${TARGET}.dylib"
else
	DYLIB_WORKAROUND = cp "${INSTALLDIR}/${TARGET}" "${INSTALLDIR}/${TARGET}.so"
	LDFLAGS += -fuse-ld=gold
endif

gens := error_gen flags_gen whence_gen limits_gen filetype_gen signal_gen \
	poll_gen process_gen time_gen timer_gen pthreads_gen socket_gen

.PHONY: all
all: $(gens)

%_gen: %.c
	$(CC) $(LDFLAGS) -o $@ $^
