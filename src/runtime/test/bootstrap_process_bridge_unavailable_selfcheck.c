/* Seed-lane witness for runtime_bootstrap_process_bridge_unavailable.c.
 *
 * Regression for release.yml run 42457312983 (2026-11-08): the Linux Rust seed
 * failed to LINK because runtime_socket_nonblock.c and runtime_process_owned.c
 * reference five process-bridge symbols that only runtime_process.c defined.
 * This TU links the seed-only provider with the two consuming headers'
 * prototypes (never runtime_process.c) and proves (1) every bridge resolves,
 * (2) each answers the canonical owner's no-slot/unsupported code rather than
 * a fabricated success, and (3) out-parameters are cleared on every call.
 *
 * Build and run (Linux):
 *   clang -std=c11 -I src/runtime src/runtime/test/bootstrap_process_bridge_unavailable_selfcheck.c \
 *     src/runtime/runtime_bootstrap_process_bridge_unavailable.c -o /tmp/bridge_selfcheck && /tmp/bridge_selfcheck
 */
#include <stdint.h>
#ifndef __linux__
int main(void) { return 77; } /* Explicit unsupported host, never a PASS. */
#else
#include <assert.h>
#include <errno.h>
#include <stdio.h>
#include "../runtime_local_unix_bridge_v1.h"

int rt_process_stream_claim_launch_v2(int64_t,const char*,int64_t,const char*,int64_t,int*,int*,int*);
int rt_process_stream_launch_not_started_v2(int64_t,const char*,int64_t,const char*,int64_t);
int rt_process_stream_publish_broker_v2(int64_t,const char*,int64_t,const char*,int64_t,int64_t);

int main(void) {
    const char root[] = "/nonexistent";
    const char identity[] = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";

    int fd = 123;
    assert(simple_process_stdout_take_v1(1, 1, root, (int64_t)sizeof root - 1, identity, 64, &fd) == -4);
    assert(fd == -1);
    assert(simple_process_stdout_take_v1(1, 1, root, (int64_t)sizeof root - 1, identity, 64, NULL) == -4);

    int64_t generation = 99;
    assert(simple_process_byte_adopt_v1(0, identity, 64, &generation) == -4);
    assert(generation == 0);
    assert(simple_process_byte_adopt_v1(0, identity, 64, NULL) == -4);

    int in = 5, out = 6, dir = 7;
    assert(rt_process_stream_claim_launch_v2(1, root, (int64_t)sizeof root - 1, identity, 64, &in, &out, &dir) == ESTALE);
    assert(in == -1 && out == -1 && dir == -1);
    assert(rt_process_stream_claim_launch_v2(1, root, (int64_t)sizeof root - 1, identity, 64, NULL, &out, &dir) == EINVAL);

    assert(rt_process_stream_launch_not_started_v2(1, root, (int64_t)sizeof root - 1, identity, 64) == ESTALE);
    assert(rt_process_stream_publish_broker_v2(1, root, (int64_t)sizeof root - 1, identity, 64, 4242) == ESTALE);
    assert(rt_process_stream_publish_broker_v2(1, root, (int64_t)sizeof root - 1, identity, 64, 0) == EINVAL);

    puts("PASS bootstrap_process_bridge_unavailable: 5 seed bridges resolve and fail closed");
    return 0;
}
#endif
