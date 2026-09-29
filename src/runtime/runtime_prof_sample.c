/*
 * Env-gated SIGPROF PC sampler (diagnostic tooling).
 *
 * When SIMPLE_PROF_SAMPLE_FILE is set at process start, installs a SIGPROF
 * handler and a 100 Hz ITIMER_PROF timer in an early constructor and appends
 * the interrupted instruction pointer (raw 8-byte little-endian values) to
 * the named file for the whole process lifetime. With the env var unset the
 * constructor returns before touching signals, timers, or files: zero
 * behaviour change.
 *
 * Purpose: sample processes that cannot be reached by gdb/perf sampling,
 * e.g. a native-built Simple compiler binary running under qemu-user.
 *
 * The signal handler is strictly async-signal-safe: it reads the PC out of
 * the ucontext and issues one write(2) of 8 bytes to an O_APPEND fd opened
 * once in the constructor. No malloc, no stdio, no locks.
 *
 * Build: cc -c -O2 -std=gnu11 -fPIC runtime_prof_sample.c -o runtime_prof_sample.o
 *
 * Enabled only on Linux x86_64/aarch64 with a GNU-compatible compiler (the
 * ucontext PC layout is guarded per arch below). Every other target compiles
 * this file to an empty translation unit, so list membership is harmless
 * there.
 */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif

#if defined(__linux__) && (defined(__x86_64__) || defined(__aarch64__)) && \
    (defined(__GNUC__) || defined(__clang__))

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <sys/time.h>
#include <ucontext.h>

static int g_prof_sample_fd = -1;

static void prof_sample_sigprof(int sig, siginfo_t *info, void *ucontext) {
    (void)sig;
    (void)info;
    ucontext_t *uc = (ucontext_t *)ucontext;
    uint64_t pc = 0;
#if defined(__aarch64__)
    pc = (uint64_t)uc->uc_mcontext.pc;
#else
    /* __x86_64__: gregs[REG_RIP] requires _GNU_SOURCE (defined above). */
    pc = (uint64_t)uc->uc_mcontext.gregs[REG_RIP];
#endif
    if (g_prof_sample_fd >= 0) {
        /* O_APPEND makes each 8-byte record atomic; errors (EAGAIN et al.)
         * are deliberately ignored. */
        ssize_t ignored = write(g_prof_sample_fd, &pc, sizeof(pc));
        (void)ignored;
    }
}

/*
 * Archive-retention anchor. The runtime is normally linked as a static
 * archive with only a small set of referenced retention roots forced via
 * -Wl,-u,<root> / /INCLUDE:<root>; a constructor-only object would be
 * dropped from the archive link and the sampler would silently vanish. The
 * linker root set consults the archive's defined symbols before forcing any
 * root, so archives built without this TU simply skip the root.
 */
void prof_sample_force_link(void) {}

/* The SIGPROF handler writes the raw PC directly; the constructor prints
 * nothing (admission probes diff stderr byte-for-byte), so no stdio-free
 * emit helpers are needed here. */

/*
 * Priority 101: glibc reserves constructor priorities 0-100 for itself, so
 * this runs before every default-priority (65535) runtime/app constructor,
 * covering essentially the whole process lifetime. getenv is already usable
 * here (the loader sets up the environment before any initializer runs).
 */
__attribute__((constructor(101)))
static void prof_sample_init(void) {
    const char *path = getenv("SIMPLE_PROF_SAMPLE_FILE");
    if (path == NULL || path[0] == '\0') {
        return;
    }

    int flags = O_WRONLY | O_CREAT | O_APPEND;
#ifdef O_CLOEXEC
    flags |= O_CLOEXEC;
#endif
    int fd = open(path, flags, 0644);
    if (fd < 0) {
        /* Silent: see below — probes diff stderr byte-for-byte. */
        return;
    }
    g_prof_sample_fd = fd;

    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_sigaction = prof_sample_sigprof;
    sa.sa_flags = SA_SIGINFO;
    sigemptyset(&sa.sa_mask);
    sigaction(SIGPROF, &sa, NULL);

    struct itimerval it;
    memset(&it, 0, sizeof(it));
    it.it_value.tv_usec = 10000;     /* first tick: 10 ms */
    it.it_interval.tv_usec = 10000;  /* 100 Hz */
    setitimer(ITIMER_PROF, &it, NULL);

    /* No stderr greeting: admission probes (stage2 receiver) diff a binary's
     * stdout/stderr against expected output byte-for-byte, so any banner
     * breaks bootstrap. Activation is observable via the sample file itself
     * (O_CREAT above); open failure reports only to the sample-file sibling
     * via errno-free silence plus a nonzero exit is NOT wanted either — keep
     * failure quiet too. */
}

#else /* !(Linux x86_64/aarch64 GNU/clang) */

/* Empty translation unit on unsupported targets: the file stays in the
 * source lists but compiles to nothing and defines no symbols there. */
typedef int prof_sample_disabled_t;

#endif
