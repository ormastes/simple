/* WebGPU backfill for core-C runtime lanes.
 *
 * The hosted wgpu backend lives in the Rust runtime only
 * (src/runtime/hosted/webgpu.rs). These fail-closed definitions exist so a
 * core-C link of a closure reaching std.gpu.engine2d.webgpu_sffi still has an
 * owner for all six rt_webgpu_* externs (macOS Stage-4, 2026-09-06): the lane
 * has no wgpu provider, so acquisition reports unavailable and teardown has
 * nothing to release.
 *
 * They are a separate translation unit ON PURPOSE. Inside runtime_native.c
 * they rode along whenever that object was pulled for any other symbol, so
 * the Windows host-gpu link (hosted runtime rlib + core-C runtime, no
 * `-z muldefs` equivalent on COFF) failed with duplicate rt_webgpu_init /
 * rt_webgpu_create_surface / rt_webgpu_destroy_surface. As their own archive
 * member they are pulled only when no earlier input (the hosted rlib) already
 * defines them. */

#include <stdbool.h>
#include <stdint.h>

bool rt_webgpu_is_available(void) { return false; }
bool rt_webgpu_init(void) { return false; }
int64_t rt_webgpu_create_surface(int32_t width, int32_t height) {
    (void)width;
    (void)height;
    return 0;
}
bool rt_webgpu_shutdown(void) { return false; }
bool rt_webgpu_destroy_surface(int64_t handle) {
    (void)handle;
    return false;
}
