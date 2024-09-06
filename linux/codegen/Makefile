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
all: inotify_gen signalfd_gen timerfd_gen

inotify_gen: inotify.c
	$(CC) $(LDFLAGS) -o inotify_gen inotify.c

signalfd_gen: signalfd.c
	$(CC) $(LDFLAGS) -o signalfd_gen signalfd.c

timerfd_gen: timerfd.c
	$(CC) $(LDFLAGS) -o timerfd_gen timerfd.c
