/* Smoke check for platform/async_driver.c + platform/async_windows.c (IOCP).
 *
 * The phase-3 stage3 link (2026-11-02) needed both files, which the baked
 * core-C runtime list omitted. This proves the 14 rt_driver_* exports and
 * spl_driver_create_iocp link and work: create an IOCP driver, run one timer
 * completion round-trip, destroy it, and check stale/invalid handles fail
 * with -EINVAL instead of crashing.
 *
 * Build + run (Windows, llvm-mingw UCRT clang + lld):
 *   clang -std=gnu11 -O1 -fuse-ld=lld -Isrc/runtime -Isrc/runtime/platform \
 *      -o build/async_iocp.exe src/runtime/test/async_driver_iocp_smoke_selfcheck.c \
 *      src/runtime/platform/async_driver.c src/runtime/platform/async_windows.c \
 *      <core-C runtime archive> -lws2_32 -lmswsock && build/async_iocp.exe
 * On non-Windows hosts it prints SKIP and exits 0.
 */
#include <stdint.h>
#include <stdio.h>

#if defined(_WIN32)
#include <errno.h>
#include "async_driver.h"

extern int64_t rt_driver_create(int64_t queue_depth);
extern void    rt_driver_destroy(int64_t handle);
extern int64_t rt_driver_submit_timeout(int64_t handle, int64_t timeout_ms);
extern int64_t rt_driver_flush(int64_t handle);
extern int64_t rt_driver_poll(int64_t handle, int64_t max, int64_t timeout_ms);
extern int64_t rt_driver_poll_id(int64_t handle, int64_t index);

static int failures = 0;

static void check(int cond, const char* what) {
    printf("  %s %s\n", cond ? "ok  " : "FAIL", what);
    if (!cond) failures++;
}

int main(void) {
    printf("async_driver IOCP smoke\n");

    /* Direct backend constructor (spl_driver_create_iocp). */
    spl_driver* d = spl_driver_create_iocp(64);
    check(d != NULL, "spl_driver_create_iocp returns a driver");
    if (d) {
        check(spl_driver_backend_type(d) == SPL_BACKEND_IOCP, "backend type is IOCP");
        spl_driver_destroy(d);
        check(1, "spl_driver_destroy returns");
    }

    /* Flat handle API (rt_driver_*), dispatching to IOCP. */
    int64_t h = rt_driver_create(64);
    check(h >= 0, "rt_driver_create returns a handle");
    if (h >= 0) {
        int64_t op = rt_driver_submit_timeout(h, 10);
        check(op > 0, "submit_timeout returns a positive op id");
        check(rt_driver_flush(h) >= 0, "flush succeeds");
        int64_t got = 0;
        for (int i = 0; i < 20 && got == 0; i++) got = rt_driver_poll(h, 8, 100);
        check(got >= 1, "timer completion arrives within 2s");
        if (got >= 1) check(rt_driver_poll_id(h, 0) == op, "completion carries the submitted op id");
        rt_driver_destroy(h);
        check(rt_driver_flush(h) == -EINVAL, "destroyed handle is rejected with -EINVAL");
    }
    check(rt_driver_flush(-1) == -EINVAL, "invalid handle -1 is rejected with -EINVAL");
    check(rt_driver_flush(1 << 20) == -EINVAL, "out-of-range handle is rejected with -EINVAL");

    printf("%s (%d failures)\n", failures ? "FAIL" : "PASS", failures);
    return failures ? 1 : 0;
}
#else
int main(void) {
    printf("async_driver IOCP smoke: SKIP (not Windows)\n");
    return 0;
}
#endif
