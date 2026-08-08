/*
 * rt_socket_set_nonblocking -- portable O_NONBLOCK toggle for a POSIX fd.
 *
 * The only prior definition lives in src/runtime/platform/async_linux_epoll.c
 * (verbatim body copied below, unchanged), which is:
 *   (a) gated `#if defined(__linux__)` for the whole translation unit, and
 *   (b) not compiled by either the interpreter/seed crate's own C-source
 *       list (src/compiler_rust/runtime/build.rs) or the native-product-build
 *       list (src/compiler/70.backend/backend/runtime_compiler.spl), so
 *       rt_socket_set_nonblocking died with "unknown extern function" from
 *       every hosted path -- doc/08_tracking/bug/interpreter_extern_unreachable_names.md
 *       bucket (a).
 *
 * Pulling the whole async_linux_epoll.c file in to get this one function
 * would drag in its epoll/timerfd/threadpool machinery (spl_driver_create_epoll
 * and friends) and a hard dependency on spl_array_new_i64/spl_array_push_i64
 * (defined in runtime.c, which this crate does not compile -- the same
 * SplArray-marshalling problem the rt_audio_play_pcm_f32 precedent hit in
 * runtime_audio.c). rt_socket_set_nonblocking itself has neither dependency:
 * it is pure fcntl(2), so it is extracted verbatim into its own small
 * translation unit instead, matching the runtime_native_gpu_stub.c partial-
 * extraction precedent (src/compiler_rust/runtime/build.rs).
 *
 * fcntl(F_GETFL/F_SETFL, O_NONBLOCK) is standard POSIX, not Linux-specific,
 * so the gate here is widened to "any non-Windows target" rather than
 * reproducing the Linux-only gate of the epoll file it was extracted from --
 * this is strictly more capable, never less, than the code it replaces.
 */

#if !defined(_WIN32)

#include <fcntl.h>
#include <stdbool.h>
#include <stdint.h>

bool rt_socket_set_nonblocking(int64_t fd, bool enabled) {
    int flags = fcntl((int)fd, F_GETFL, 0);
    if (flags < 0) return false;
    if (enabled) {
        flags |= O_NONBLOCK;
    } else {
        flags &= ~O_NONBLOCK;
    }
    return (fcntl((int)fd, F_SETFL, flags) == 0);
}

#endif /* !defined(_WIN32) */
