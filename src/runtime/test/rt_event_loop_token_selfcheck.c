/* rt_event_loop_* token/readiness contract (bugs 2026-11-28
 * c_epoll_token_table_process_wide + kqueue_poll_readwrite_two_events).
 *   - the token is per loop: one fd in two loops keeps each loop's token;
 *   - deregister + re-register replaces the token; an unknown fd reports fd;
 *   - a mode-2 fd that is both readable and writable is ONE entry, ready == 2
 *     (epoll and kqueue alike).
 * Uses real epoll/kqueue on a socketpair. Other platforms exit 77 (skip). */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#include "../runtime_native.c"
#include <stdio.h>
/* Always evaluates: survives -DNDEBUG, unlike assert(). */
#define CHECK(c) do { if (!(c)) { fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, #c); return 1; } } while (0)
#if !defined(__linux__) && !defined(__APPLE__) && !defined(__FreeBSD__)
int main(void){return 77;}
#else
#include <sys/socket.h>
int main(void) {
    int sv[2];
    CHECK(socketpair(AF_UNIX, SOCK_STREAM, 0, sv) == 0);
    CHECK(write(sv[1], "x", 1) == 1); /* sv[0]: readable and writable */
    int64_t a = rt_event_loop_create(), b = rt_event_loop_create();
    CHECK(a >= 0 && b >= 0 && a != b);
    CHECK(rt_event_loop_register(a, sv[0], 0, 111, 0) == 1);
    CHECK(rt_event_loop_register(b, sv[0], 0, 222, 0) == 1);
    CHECK(rt_event_loop_poll(a, 8, 1000) == 1);
    CHECK(rt_event_loop_poll_get_fd(0) == sv[0] && rt_event_loop_poll_get_token(0) == 111);
    CHECK(rt_event_loop_poll(b, 8, 1000) == 1);
    CHECK(rt_event_loop_poll_get_token(0) == 222);
    CHECK(rt_event_loop_deregister(a, sv[0]) == 1);
    CHECK(rt_event_loop_register(a, sv[0], 2, 333, 0) == 1);
    CHECK(rt_event_loop_poll(a, 8, 1000) == 1);
    CHECK(rt_event_loop_poll_get_ready(0) == 2 && rt_event_loop_poll_get_token(0) == 333);
    CHECK(rt_event_loop_poll(-1, 8, 0) == 0);
    /* write-only (mode 1) registration must be fully removed by deregister */
    CHECK(rt_event_loop_deregister(b, sv[0]) == 1);
    CHECK(rt_event_loop_register(b, sv[1], 1, 444, 0) == 1);
    CHECK(rt_event_loop_deregister(b, sv[1]) == 1);
    CHECK(rt_event_loop_poll(b, 8, 0) == 0);
    rt_event_loop_close(a);
    rt_event_loop_close(b);
    close(sv[0]);
    close(sv[1]);
    return 0;
}
#endif
