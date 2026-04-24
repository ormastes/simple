/*
 * Hosted (non-baremetal) fallback stubs for the Simple log-lib runtime hooks.
 *
 * When the log lib's extern symbols return false, the Simple-side code
 * falls through to its interpreter-safe path (println / stdio). These
 * stubs exist so log-lib consumers link cleanly on Linux/macOS/Windows
 * and the spec harness can load test/os/kernel/log/*_spec.spl.
 *
 * The baremetal implementations live in
 * src/runtime/startup/baremetal/runtime_log.c and are linked instead
 * for SimpleOS kernel/device builds.
 */

#include <stdint.h>
#include <stdbool.h>

bool rt_simpleos_log_init(int64_t level, int64_t targets) {
    (void)level; (void)targets;
    return false;
}

bool rt_simpleos_log_is_enabled(int64_t level) {
    (void)level;
    return false;
}

bool rt_simpleos_log_emit(int64_t level, int64_t msg_ptr, int64_t msg_len) {
    (void)level; (void)msg_ptr; (void)msg_len;
    return false;
}

bool rt_log_target_device_write_bytes(int64_t ptr, int64_t len) {
    (void)ptr; (void)len;
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
