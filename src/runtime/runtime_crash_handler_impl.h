/* runtime_crash_handler_impl.h -- private crash signal handler shared by
 * runtime.c and runtime_native.c.
 *
 * Not a public header: include it once per translation unit after standard
 * headers (<stdio.h>, <stdint.h>, <string.h>, <signal.h>, and <unistd.h> on
 * POSIX). Everything here is static; the exported rt_install_crash_handler
 * stays hand-written in each includer so each lane keeps its linkage. */
#ifndef SIMPLE_RUNTIME_CRASH_HANDLER_IMPL_H
#define SIMPLE_RUNTIME_CRASH_HANDLER_IMPL_H

#if !defined(_WIN32) && !defined(__EMSCRIPTEN__) && !defined(__simpleos__)
#  if !defined(SPL_HAVE_EXECINFO)
#    if defined(__APPLE__) || defined(__GLIBC__) || defined(__FreeBSD__)
#      if defined(__has_include)
#        if __has_include(<execinfo.h>)
#          include <execinfo.h>
#          define SPL_HAVE_EXECINFO 1
#        endif
#      else
#        include <execinfo.h>
#        define SPL_HAVE_EXECINFO 1
#      endif
#    endif
#  endif

/* Classify a fault from siginfo_t.si_code.
 *
 * Phase 5 of doc/03_plan/infra/audit/serial_sigsegv_and_test_hardening.md:
 * si_addr alone cannot tell a wild-pointer dereference apart from a fault the
 * process brought on itself by exhausting a resource, and the two need
 * different operator responses (fix the pointer bug vs. raise the limit).
 * Pure lookup, no allocation, no locking — safe to call from a signal handler. */
static const char* _spl_fault_class(int signum, int sicode) {
    if (sicode == SI_USER) return "delivered by kill() — not a genuine fault";
#ifdef SI_KERNEL
    if (sicode == SI_KERNEL) return "kernel-raised fault";
#endif
    if (signum == SIGSEGV) {
        if (sicode == SEGV_MAPERR) return "address not mapped — wild/null pointer";
        /* A guard page (stack overflow, or an mmap'd region past a limit) is
         * mapped but not accessible, so a resource-limit violation lands here
         * rather than on SEGV_MAPERR. */
        if (sicode == SEGV_ACCERR) return "permission denied on a mapped page — guard page / memory-limit violation";
#ifdef SEGV_BNDERR
        if (sicode == SEGV_BNDERR) return "bounds-check violation";
#endif
        return "unclassified segmentation fault";
    }
    if (sicode == BUS_ADRALN) return "misaligned address";
    if (sicode == BUS_ADRERR) return "nonexistent physical address";
    if (sicode == BUS_OBJERR) return "object-specific hardware error";
    return "unclassified bus error";
}

static void _spl_crash_handler(int signum, siginfo_t *info, void *ucontext) {
    (void)ucontext;
    const char *signame = (signum == SIGSEGV) ? "SIGSEGV" : "SIGBUS";
    int sicode = info ? info->si_code : 0;
    void *siaddr = info ? info->si_addr : NULL;

    /* Use write() not fprintf — async-signal-safe.
     * Clamp snprintf() return value so truncated formatting never over-reads buf. */
    char buf[256];
    int len = snprintf(buf, sizeof(buf),
        "\n[simple-runtime] Fatal: %s at address %p (si_code=%d: %s)\n",
        signame, siaddr, sicode, _spl_fault_class(signum, sicode));
    if (len > 0) {
        size_t write_len = (size_t)len < sizeof(buf) ? (size_t)len : sizeof(buf) - 1U;
        ssize_t ignored = write(STDERR_FILENO, buf, write_len);
        (void)ignored;
    }

    /* Backtrace */
#ifdef SPL_HAVE_EXECINFO
    void *frames[32];
    int nframes = backtrace(frames, 32);
    if (nframes > 0) {
        ssize_t ignored = write(STDERR_FILENO, "Backtrace:\n", 11);
        (void)ignored;
        backtrace_symbols_fd(frames, nframes, STDERR_FILENO);
    }
#endif

    /* Exit with signal-appropriate code */
    _exit(128 + signum);
}

static int64_t rt_install_crash_handler_impl(void) {
    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_sigaction = _spl_crash_handler;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = SA_SIGINFO | SA_RESETHAND;

    int ok = 1;
    if (sigaction(SIGSEGV, &sa, NULL) == -1) ok = 0;
    if (sigaction(SIGBUS, &sa, NULL) == -1) ok = 0;
    return ok;
}
#else
static int64_t rt_install_crash_handler_impl(void) {
    return 0;
}
#endif

#endif /* SIMPLE_RUNTIME_CRASH_HANDLER_IMPL_H */
