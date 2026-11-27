#if defined(_WIN32)
#include <stdio.h>
int main(void) {
    puts("SKIP: rt_fork_crash_handler_darwin_test requires POSIX fork/sigaction");
    return 0;
}
#else
#include "runtime.h"
#include "runtime_fork.h"

#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

static int g_checks = 0;
static int g_failures = 0;

#define CHECK(cond) do { \
    ++g_checks; \
    if (!(cond)) { \
        ++g_failures; \
        fprintf(stderr, "FAIL line %d: %s\n", __LINE__, #cond); \
    } \
} while (0)

__attribute__((noinline))
static void trigger_null_write(void) {
    volatile int64_t* volatile p = (volatile int64_t*)0;
    *p = 1;
}

int main(int argc, char** argv) {
    /* 1. Startup hook installs the crash handler via spl_init_args, and clean
     *    forked child returns rc=0 with signaled==false. */
    spl_init_args(argc, argv);

    int64_t pid = rt_fork_child_setup();
    if (pid == 0) {
        if (rt_install_crash_handler() != 1) {
            rt_fork_child_exit(99);
        }
        fputs("clean-stdout\n", stdout);
        fflush(NULL);
        rt_fork_child_exit(0);
    }
    CHECK(pid > 0);
    CHECK(rt_fork_parent_wait(pid, 10000) == 0);
    CHECK(!rt_fork_parent_signaled());
    CHECK(!rt_fork_parent_timed_out());
    CHECK(strstr(rt_fork_parent_stdout(), "clean-stdout") != NULL);

    /* 2. Forked null-pointer dereference with crash handler inherited from
     *    spl_init_args() exits 128+SIGSEGV (139), signaled==false, and emits
     *    the Fatal banner, si_code classification, and Backtrace. */
    pid = rt_fork_child_setup();
    if (pid == 0) {
        trigger_null_write();
        rt_fork_child_exit(98);
    }
    CHECK(pid > 0);
    int64_t rc = rt_fork_parent_wait(pid, 10000);
#if defined(__APPLE__)
    CHECK(rc == 139);
#else
    CHECK(rc == 128 + SIGSEGV || rc == 128 + SIGBUS);
#endif
    CHECK(!rt_fork_parent_signaled());
    CHECK(strstr(rt_fork_parent_stderr(), "[simple-runtime] Fatal:") != NULL);
    CHECK(strstr(rt_fork_parent_stderr(), "si_code=") != NULL);
    CHECK(strstr(rt_fork_parent_stderr(), "Backtrace:") != NULL);

    /* 3. Explicit rt_install_crash_handler() in forked child + null write. */
    pid = rt_fork_child_setup();
    if (pid == 0) {
        signal(SIGSEGV, SIG_DFL);
        signal(SIGBUS, SIG_DFL);
        if (rt_install_crash_handler() != 1) {
            rt_fork_child_exit(99);
        }
        trigger_null_write();
        rt_fork_child_exit(98);
    }
    CHECK(pid > 0);
    rc = rt_fork_parent_wait(pid, 10000);
#if defined(__APPLE__)
    CHECK(rc == 139);
#else
    CHECK(rc == 128 + SIGSEGV || rc == 128 + SIGBUS);
#endif
    CHECK(!rt_fork_parent_signaled());
    CHECK(strstr(rt_fork_parent_stderr(), "[simple-runtime] Fatal: SIGSEGV") != NULL);
    CHECK(strstr(rt_fork_parent_stderr(), "Backtrace:") != NULL);

    /* 4. SIGBUS is also intercepted by _spl_crash_handler (Darwin arm64 uses
     *    SIGBUS for misaligned/guard faults). */
    pid = rt_fork_child_setup();
    if (pid == 0) {
        if (rt_install_crash_handler() != 1) {
            rt_fork_child_exit(99);
        }
        kill(getpid(), SIGBUS);
        rt_fork_child_exit(98);
    }
    CHECK(pid > 0);
    rc = rt_fork_parent_wait(pid, 10000);
    CHECK(rc == 128 + SIGBUS);
    CHECK(!rt_fork_parent_signaled());
    CHECK(strstr(rt_fork_parent_stderr(), "[simple-runtime] Fatal: SIGBUS") != NULL);
    CHECK(strstr(rt_fork_parent_stderr(), "Backtrace:") != NULL);

    /* 5. Without the crash handler, a null write dies by raw signal. */
    pid = rt_fork_child_setup();
    if (pid == 0) {
        signal(SIGSEGV, SIG_DFL);
        signal(SIGBUS, SIG_DFL);
        trigger_null_write();
        rt_fork_child_exit(98);
    }
    CHECK(pid > 0);
    rc = rt_fork_parent_wait(pid, 10000);
    CHECK(rt_fork_parent_signaled());
    CHECK(strstr(rt_fork_parent_stderr(), "[simple-runtime] Fatal:") == NULL);

    printf("rt_fork_crash_handler_darwin_test: %d checks, %d failures\n", g_checks, g_failures);
    return g_failures ? 1 : 0;
}
#endif
