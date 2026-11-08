/* Hosted Rust seed's Linux process-bridge "unavailable" provider.
 *
 * runtime_process.c owns the canonical piped-process registry (s_procs /
 * s_proc_lock) and with it the native-private bridges that
 * runtime_socket_nonblock.c (runtime_local_unix_transfer_v1.h) and
 * runtime_process_owned.c (runtime_linux_group_owner_impl.h) call on Linux:
 *
 *   simple_process_stdout_take_v1 / simple_process_byte_adopt_v1
 *   rt_process_stream_claim_launch_v2 / rt_process_stream_launch_not_started_v2 /
 *   rt_process_stream_publish_broker_v2
 *
 * The seed cannot compile runtime_process.c (it collides with Rust-owned
 * rt_process_* APIs), so without this translation unit every Linux seed link
 * fails with "undefined symbol" for the five names above (release.yml run
 * 42457312983, job 128659173410, 2026-11-08). The seed has no piped registry,
 * so each bridge answers exactly what the canonical owner answers when no
 * stream/endpoint slot exists: -4 (unsupported lane) for the v1 byte-endpoint
 * bridges and ESTALE for the v2 stream bridges, with every out-parameter
 * cleared. Nothing is fabricated as success.
 *
 * Seed-only: the full C runtime links runtime_process.c, never this file.
 * Covered by src/runtime/test/bootstrap_process_bridge_unavailable_selfcheck.c.
 */
#if defined(__linux__)
#include <errno.h>
#include <stdint.h>

int64_t simple_process_stdout_take_v1(int64_t pid, int64_t generation,
        const char* root, int64_t root_bytes, const char* identity, int64_t identity_bytes, int* fd) {
    (void)pid; (void)generation; (void)root; (void)root_bytes; (void)identity; (void)identity_bytes;
    if (fd) *fd = -1;
    return -4;
}

int64_t simple_process_byte_adopt_v1(int fd, const char* binding, int64_t binding_bytes, int64_t* generation) {
    (void)fd; (void)binding; (void)binding_bytes;
    if (generation) *generation = 0;
    return -4;
}

int rt_process_stream_claim_launch_v2(int64_t generation, const char* root, int64_t root_len,
        const char* identity, int64_t identity_len, int* input, int* output, int* root_fd) {
    (void)generation; (void)root; (void)root_len; (void)identity; (void)identity_len;
    if (!input || !output || !root_fd) return EINVAL;
    *input = -1; *output = -1; *root_fd = -1;
    return ESTALE;
}

int rt_process_stream_launch_not_started_v2(int64_t generation, const char* root, int64_t root_len,
        const char* identity, int64_t identity_len) {
    (void)generation; (void)root; (void)root_len; (void)identity; (void)identity_len;
    return ESTALE;
}

int rt_process_stream_publish_broker_v2(int64_t generation, const char* root, int64_t root_len,
        const char* identity, int64_t identity_len, int64_t broker_pid) {
    (void)generation; (void)root; (void)root_len; (void)identity; (void)identity_len;
    if (broker_pid <= 0) return EINVAL;
    return ESTALE;
}
#else
typedef int simple_bootstrap_process_bridge_unavailable_unused_t;
#endif
