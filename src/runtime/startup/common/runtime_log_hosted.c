/*
 * Hosted (non-baremetal) fallback stubs for the Simple log-lib runtime hooks.
 *
 * When the log lib's extern symbols return false, the Simple-side code
 * falls through to its interpreter-safe path (println / stdio). These
 * stubs exist so log-lib consumers link cleanly on Linux/macOS/Windows
 * and the spec harness can load test/unit/os/kernel/logging/*_spec.spl.
 *
 * The baremetal implementations live in
 * src/runtime/startup/baremetal/runtime_log.c and are linked instead
 * for SimpleOS kernel/device builds.
 */

#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>

/*
 * Level-gated emission probe -- DEFAULT OFF, costs one getenv on first use.
 *
 * These stubs returning a bare `false` is why
 * doc/08_tracking/bug/jit_rt_string_data_returns_nil_breaking_extern_calls_2026-08-10.md
 * stayed invisible for so long: the hosted path could not distinguish "the
 * (ptr,len) marshal delivered a real string and the hook is stubbed" from "the
 * marshal handed me garbage". Both return false, both take the Simple-side
 * fallthrough, and the log line still appears. On a baremetal build, where this
 * hook is the real UART emitter, the second case silently loses every line.
 *
 * With SIMPLE_LOG_HOSTED_PROBE=1 the stub writes what it actually RECEIVED to
 * fd 2, labelled, so a check can assert the payload rather than a line count.
 * The return value is unchanged in both modes, so the hosted contract and every
 * existing logging check are untouched.
 */
static int rt_log_hosted_probe_on(void) {
    static int cached = -1;
    if (cached < 0) {
        const char *v = getenv("SIMPLE_LOG_HOSTED_PROBE");
        cached = (v && v[0] == '1' && v[1] == '\0') ? 1 : 0;
    }
    return cached;
}

static void rt_log_hosted_probe(const char *tag, int64_t level, int64_t ptr, int64_t len) {
    char head[64];
    int n;
    if (!rt_log_hosted_probe_on()) {
        return;
    }
    n = snprintf(head, sizeof(head), "[HOSTED-LOG-PROBE] %s level=%lld len=%lld payload=",
                 tag, (long long)level, (long long)len);
    if (n > 0) {
        ssize_t ignored = write(2, head, (size_t)n);
        (void)ignored;
    }
    /* Only dereference a plausible pointer/length pair -- the whole point of
     * the probe is that a broken marshal may hand us nonsense. */
    if (ptr != 0 && len > 0 && len < 4096) {
        ssize_t ignored = write(2, (const void *)(intptr_t)ptr, (size_t)len);
        (void)ignored;
    } else {
        ssize_t ignored = write(2, "<UNREADABLE>", 12);
        (void)ignored;
    }
    {
        ssize_t ignored = write(2, "\n", 1);
        (void)ignored;
    }
}

bool rt_simpleos_log_init(int64_t level, int64_t targets) {
    (void)level; (void)targets;
    return false;
}

bool rt_simpleos_log_is_enabled(int64_t level) {
    (void)level;
    return false;
}

bool rt_simpleos_log_emit(int64_t level, int64_t msg_ptr, int64_t msg_len) {
    rt_log_hosted_probe("emit", level, msg_ptr, msg_len);
    return false;
}

bool rt_log_target_device_write_bytes(int64_t ptr, int64_t len) {
    rt_log_hosted_probe("device_write", -1, ptr, len);
    return false;
}

bool rt_log_target_semihost_write_bytes(int64_t ptr, int64_t len) {
    (void)ptr; (void)len;
    return false;
}

bool rt_simpleos_log_set_device(int64_t kind, int64_t base) {
    (void)kind; (void)base;
    return false;
}
