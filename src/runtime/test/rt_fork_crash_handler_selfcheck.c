/* Fork bridge + crash handler selfcheck (POSIX).
 *
 * Bug: doc/08_tracking/bug/crash_handler_and_fork_bridge_absent_from_seed_macos_2026-09-06.md
 *
 * Drives the real C runtime symbols directly:
 *   1. rt_fork_child_setup / rt_fork_parent_wait capture a clean child's
 *      stdout+stderr and exit code.
 *   2. A child that installs rt_install_crash_handler() and writes through a
 *      null pointer exits 128+SIGSEGV (139 on Linux/BSD; macOS may deliver
 *      SIGBUS -> 138) via the handler's _exit, so the parent sees
 *      WIFEXITED (signaled == false) and stderr carries the
 *      "[simple-runtime] Fatal:" banner plus "Backtrace:".
 *   3. A child WITHOUT the handler dies by the raw signal: signaled == true.
 *
 * Build (from repo root, macOS/Linux/BSD):
 *   cc -Isrc/runtime src/runtime/test/rt_fork_crash_handler_selfcheck.c \
 *      src/runtime/runtime.c src/runtime/runtime_fork.c src/runtime/runtime_memtrack.c \
 *      src/runtime/runtime_simd_utf8.c -Wl,-undefined,dynamic_lookup -o fc  # macOS
 *   (Linux: -Wl,--unresolved-symbols=ignore-all; runtime.c references array/string
 *   helpers from runtime_native.c that the fork/crash paths never call.)
 *   Measured macOS arm64 2026-11-04: crash child rc=139, 15 checks, 0 failures.
 */
#include "../runtime_fork.h"

#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

int64_t rt_install_crash_handler(void);

static int checks, failures;
#define CHECK(c) do { ++checks; if (!(c)) { ++failures; \
    fprintf(stderr, "FAIL fork/crash line %d: %s\n", __LINE__, #c); } } while (0)

static void null_write(void) {
    volatile int64_t* volatile p = (volatile int64_t*)0;
    *p = 1;
}

int main(void) {
    /* 1. clean child */
    int64_t pid = rt_fork_child_setup();
    if (pid == 0) {
        fputs("child-out\n", stdout);
        fputs("child-err\n", stderr);
        fflush(NULL);
        _exit(7);
    }
    CHECK(pid > 0);
    CHECK(rt_fork_parent_wait(pid, 10000) == 7);
    CHECK(!rt_fork_parent_signaled());
    CHECK(!rt_fork_parent_timed_out());
    CHECK(strstr(rt_fork_parent_stdout(), "child-out") != NULL);
    CHECK(strstr(rt_fork_parent_stderr(), "child-err") != NULL);

    /* 2. crash handler intercepts a null write */
    pid = rt_fork_child_setup();
    if (pid == 0) {
        if (rt_install_crash_handler() != 1) _exit(99);
        null_write();
        _exit(98);
    }
    CHECK(pid > 0);
    int64_t rc = rt_fork_parent_wait(pid, 10000);
    CHECK(rc == 128 + SIGSEGV || rc == 128 + SIGBUS);
    CHECK(!rt_fork_parent_signaled());
    CHECK(strstr(rt_fork_parent_stderr(), "[simple-runtime] Fatal:") != NULL);
    CHECK(strstr(rt_fork_parent_stderr(), "Backtrace:") != NULL);
    CHECK(strstr(rt_fork_parent_stderr(), "si_code=") != NULL);
    printf("crash child rc=%lld\n", (long long)rc);
    if (failures) fprintf(stderr, "crash child rc=%lld stderr=<<%s>>\n",
                          (long long)rc, rt_fork_parent_stderr());

    /* 3. no handler: the raw signal is observed */
    pid = rt_fork_child_setup();
    if (pid == 0) {
        signal(SIGSEGV, SIG_DFL);
        signal(SIGBUS, SIG_DFL);
        null_write();
        _exit(98);
    }
    CHECK(pid > 0);
    rc = rt_fork_parent_wait(pid, 10000);
    CHECK(rt_fork_parent_signaled());
    CHECK(strstr(rt_fork_parent_stderr(), "[simple-runtime] Fatal:") == NULL);

    printf("rt_fork_crash_handler_selfcheck: %d checks, %d failures\n", checks, failures);
    return failures ? 1 : 0;
}
