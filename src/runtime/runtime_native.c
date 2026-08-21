/*
 * Simple Native Runtime Bridge
 *
 * Provides the rt_* symbols that the LLVM IR backend declares via
 * generate_runtime_declarations_for_target(). Each function bridges
 * to the corresponding spl_* implementation in runtime.c or to libc.
 *
 * Also provides __simple_runtime_init() and __simple_runtime_shutdown()
 * called by the entry point wrapper (entry_point.spl).
 *
 * Build: cc -c -fPIC -O2 -std=gnu11 -I. -Iplatform runtime_native.c -o runtime_native.o
 */

/* Only include runtime.h for spl_* declarations — platform functions
 * (rt_dir_create, rt_sleep_ms_native, etc.) are already compiled via
 * runtime.c + platform headers. We must NOT include platform/platform.h
 * here to avoid duplicate symbol definitions. */
#include "runtime.h"
#include "runtime_simd_dispatch.h"
#include "runtime_memory_guard.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <errno.h>
#include <math.h>
#include <signal.h>
#include <time.h>
#include <stdatomic.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#if defined(_WIN32)
#include <io.h>
#include <malloc.h>
#include <windows.h>
#endif
#if !defined(_WIN32)
#include <netdb.h>
#include <dlfcn.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <arpa/inet.h>
#include <poll.h>
#include <pthread.h>
#endif

/* C-string worker; the public (ptr, len) entry point is below. Named to match
 * the workers in platform/unix_common.h and platform/platform_win.h. */
bool rt_dir_create_cpath(const char* path, bool recursive) {
    if (!path || !*path) return false;
    if (!recursive) {
#if defined(_WIN32)
        return _mkdir(path) == 0 || errno == EEXIST;
#else
        return mkdir(path, 0755) == 0 || errno == EEXIST;
#endif
    }

    char* tmp = spl_strdup(path);
    if (!tmp) return false;
    size_t len = strlen(tmp);
    while (len > 1 && (tmp[len - 1] == '/' || tmp[len - 1] == '\\')) {
        tmp[--len] = '\0';
    }
    for (char* p = tmp + 1; *p; p++) {
        if (*p == '/' || *p == '\\') {
            char saved = *p;
            *p = '\0';
#if defined(_WIN32)
            if (_mkdir(tmp) != 0 && errno != EEXIST) {
#else
            if (mkdir(tmp, 0755) != 0 && errno != EEXIST) {
#endif
                *p = saved;
                free(tmp);
                return false;
            }
            *p = saved;
        }
    }
#if defined(_WIN32)
    bool ok = _mkdir(tmp) == 0 || errno == EEXIST;
#else
    bool ok = mkdir(tmp, 0755) == 0 || errno == EEXIST;
#endif
    free(tmp);
    return ok;
}

#define RT_VALUE_TAG_MASK 0x7ULL
#define RT_VALUE_TAG_INT 0x0ULL
#define RT_VALUE_TAG_HEAP 0x1ULL
#define RT_VALUE_TAG_FLOAT 0x2ULL
#define RT_VALUE_TAG_SPECIAL 0x3ULL
#define RT_VALUE_SPECIAL_NIL 0x0ULL
#define RT_VALUE_SPECIAL_TRUE 0x1ULL
#define RT_VALUE_SPECIAL_FALSE 0x2ULL
#define RT_VALUE_HEAP_STRING 0x53545231U
#define RT_VALUE_HEAP_ARRAY 0x02U
#define RT_VALUE_HEAP_CLOSURE 0x03U
#define RT_VALUE_HEAP_ENUM 0x04U
#define RT_VALUE_HEAP_DICT 0x06U
#define RT_VALUE_HEAP_MUTEX 0x09U
/* Heap-boxed f64 (lossless container float). The inline TAG_FLOAT form stored
 * only (bits & ~7) | TAG_FLOAT, silently zeroing the low 3 mantissa bits, so a
 * container/Any float lost precision ([0.1][0] != 0.1). Container floats are now
 * boxed as an RtCoreFloat holding the full double. Distinct magic "FLT1" (like
 * RT_VALUE_HEAP_STRING's "STR1") so a validated pointer's kind read is
 * unambiguous. */
#define RT_VALUE_HEAP_FLOAT 0x464C5431U
/* Heap-boxed WIDE integer (see rt_value_int_wide). The tagged-immediate form
 * `v << 3` has only a 61-bit payload, so any |v| >= 2^60 silently sign-extended
 * back to a different number (2^60 -> negative, i64::MAX -> -1, 2^62 -> 0; bug
 * int61_bit_truncation_jit_scalars_and_native_container_boxing_2026-08-09). Per
 * doc/04_architecture/compiler/array_value_abi_contract.md §1.1 the encoder MUST
 * heap-box rather than truncate. Layout is deliberately identical to
 * RtCoreFloat, so every lifecycle switch treats it as the same leaf shape.
 * Magic "INT1". */
#define RT_VALUE_HEAP_INT 0x494E5431U
/* Heap-boxed UNSIGNED 64-bit integer (see rt_value_u64). A u64 whose top bits
 * are set fits neither the 61-bit tagged immediate nor the SIGNED wide box
 * (2^63 would read back negative), so unsigned values that exceed the signed
 * fast path get their own leaf box carrying the raw u64 verbatim.
 *
 * The magic is NOT free to choose and deliberately breaks the "…1" suffix
 * pattern of STR1/FLT1/INT1: it is fixed by the pure-Simple twin of this ABI,
 * src/runtime/simple_core/core_values.spl:33, which stores 0x55494E54 ("UINT")
 * at offset 0 and is read back with a 32-bit mask at six further call sites
 * (core_values.spl:25,40, core_bdd.spl:39, core_array_query.spl:38,
 * core_string.spl:507,518,519). Both implementations must agree byte-for-byte,
 * so this constant is copied from there rather than invented. It collides with
 * neither "STR1"/"FLT1"/"INT1" nor the small single-byte kinds (0x02..0x09).
 *
 * Layout is deliberately identical to RtCoreFloat/RtCoreWideInt (32-bit kind,
 * 32-bit transient scope id, 8-byte payload = the 16 bytes the twin's
 * `calloc(1, 16)` allocates), so every lifecycle switch treats it as the same
 * leaf shape. */
#define RT_VALUE_HEAP_UINT 0x55494E54U
#define RT_CORE_ARRAY_FLAG_BYTES 0x08U
#define RT_CORE_ARRAY_FLAG_U64_PACKED 0x10U
/* Internal-only marker distinguishing a tuple from a plain array. Both share
 * the exact same RtCoreArray representation (rt_tuple_new is literally
 * rt_array_new -- see rt_tuple_new below) and the SAME RT_VALUE_HEAP_ARRAY
 * kind byte, so nothing at runtime could tell them apart before this bit was
 * added: rt_to_string had no way to choose "(a, b)" (tuple) vs "[a, b]"
 * (array) formatting for a boxed-ANY aggregate. This flag never crosses the
 * C ABI boundary (no compiler-emitted call reads or writes it directly) and
 * does not collide with RT_CORE_ARRAY_FLAG_BYTES/U64_PACKED above, so it is
 * safe to set purely internally in rt_tuple_new. */
#define RT_CORE_ARRAY_FLAG_TUPLE 0x01U
#define RT_CORE_ARRAY_MAX_CAP 100000000LL
#define RT_HOST_GPU_LANE_HOST 1
#define RT_HOST_GPU_LANE_GPU 2
#define RT_HOST_GPU_PHASE_BEGIN 1
#define RT_HOST_GPU_PHASE_END 2
#define RT_HOST_GPU_QUEUE_STATUS_EMPTY 0
#define RT_HOST_GPU_QUEUE_STATUS_QUEUED 1
#define RT_HOST_GPU_QUEUE_STATUS_SUBMITTED 2
#define RT_HOST_GPU_QUEUE_STATUS_COMPLETED 3
#define RT_HOST_GPU_QUEUE_STATUS_UNAVAILABLE 4
#define RT_HOST_GPU_QUEUE_CAPACITY 1024

static int64_t rt_host_gpu_lane_event_total = 0;
static int64_t rt_host_gpu_lane_begin_total = 0;
static int64_t rt_host_gpu_lane_end_total = 0;
static int64_t rt_host_gpu_lane_last_lane_code = 0;
static int64_t rt_host_gpu_lane_last_phase_code = 0;
static int64_t rt_host_gpu_queue_next_packet_id = 1;
static int64_t rt_host_gpu_queue_head = 0;
static int64_t rt_host_gpu_queue_depth = 0;
static int64_t rt_host_gpu_queue_packet_total = 0;
static int64_t rt_host_gpu_queue_submitted_total = 0;
static int64_t rt_host_gpu_queue_completed_total = 0;
static int64_t rt_host_gpu_queue_last_status_code = RT_HOST_GPU_QUEUE_STATUS_EMPTY;
static int64_t rt_host_gpu_queue_last_backend_handle_value = 0;
static int64_t rt_host_gpu_queue_last_payload_size_value = 0;
static int64_t rt_host_gpu_queue_last_payload_hash_value = 0;
static int64_t rt_host_gpu_queue_last_device_time_us_value = 0;
static char rt_host_gpu_queue_last_payload_text_value[4096];
static int64_t rt_host_gpu_queue_lane_codes[RT_HOST_GPU_QUEUE_CAPACITY];
static int64_t rt_host_gpu_queue_backend_handles[RT_HOST_GPU_QUEUE_CAPACITY];
static int64_t rt_host_gpu_queue_payload_sizes[RT_HOST_GPU_QUEUE_CAPACITY];
static int64_t rt_host_gpu_queue_payload_hashes[RT_HOST_GPU_QUEUE_CAPACITY];
static char rt_host_gpu_queue_payload_texts[RT_HOST_GPU_QUEUE_CAPACITY][4096];
static int64_t rt_host_gpu_queue_in_flight_head = 0;
static int64_t rt_host_gpu_queue_in_flight_depth = 0;
static int64_t rt_host_gpu_queue_in_flight_lane_codes[RT_HOST_GPU_QUEUE_CAPACITY];
static int64_t rt_host_gpu_queue_in_flight_backend_handles[RT_HOST_GPU_QUEUE_CAPACITY];
static int64_t rt_host_gpu_queue_in_flight_payload_sizes[RT_HOST_GPU_QUEUE_CAPACITY];
static int64_t rt_host_gpu_queue_in_flight_payload_hashes[RT_HOST_GPU_QUEUE_CAPACITY];
static int64_t rt_host_gpu_queue_in_flight_submitted_at_us[RT_HOST_GPU_QUEUE_CAPACITY];
static char rt_host_gpu_queue_in_flight_payload_texts[RT_HOST_GPU_QUEUE_CAPACITY][4096];

void rt_host_gpu_queue_reset(void);

/*
 * Optional hosted GPU probes are fallback definitions only.  Native programs
 * that link a real backend provider (for example libsimple_runtime_wm.dylib
 * built with the Vulkan feature) must be allowed to bind to that provider
 * instead of being pinned to these zero-return core-runtime fallbacks.
 */
#if defined(__GNUC__) || defined(__clang__)
#define SPL_HOSTED_UNAVAILABLE_WEAK __attribute__((weak))
#else
#define SPL_HOSTED_UNAVAILABLE_WEAK
#endif

int64_t rt_cuda_available(void) { return 0; }
int64_t rt_cuda_device_count(void) { return 0; }
int32_t rt_vk_available(void) { return 0; }

typedef int64_t (*spl_hosted_i64_probe_fn)(void);

static int64_t spl_hosted_provider_i64_probe(const char* symbol) {
#if !defined(_WIN32)
    /*
     * Use a provider-only symbol name.  Looking up the public compatibility
     * name can return this executable's own weak definition under Mach-O's
     * two-level namespace instead of the strong dependent-dylib definition.
     */
    void* resolved = dlsym(RTLD_DEFAULT, symbol);
    if (resolved != NULL) {
        return ((spl_hosted_i64_probe_fn)resolved)();
    }
#else
    (void)symbol;
#endif
    return 0;
}

SPL_HOSTED_UNAVAILABLE_WEAK int64_t rt_vulkan_is_available(void) {
    return spl_hosted_provider_i64_probe("rt_vulkan_provider_is_available");
}

SPL_HOSTED_UNAVAILABLE_WEAK int64_t rt_vulkan_device_count(void) {
    return spl_hosted_provider_i64_probe("rt_vulkan_provider_device_count");
}

/*
 * Core-C parity for the runtime-owned Vulkan dependency-quarantine gate.
 * This lock is intentionally independent from any provider's Vulkan state:
 * callers invoke rt_vulkan_* operations while holding it.
 */
static atomic_flag rt_vulkan_dependency_quarantine_gate = ATOMIC_FLAG_INIT;

SPL_HOSTED_UNAVAILABLE_WEAK int64_t rt_vulkan_dependency_quarantine_lock(void) {
    while (atomic_flag_test_and_set_explicit(
        &rt_vulkan_dependency_quarantine_gate, memory_order_acquire)) { }
    return 1;
}

SPL_HOSTED_UNAVAILABLE_WEAK int64_t rt_vulkan_dependency_quarantine_unlock(void) {
    atomic_flag_clear_explicit(
        &rt_vulkan_dependency_quarantine_gate, memory_order_release);
    return 1;
}

/* Optional hosted backends are unavailable in the core C runtime. */
/* oneAPI */
bool rt_oneapi_init(void) { return false; }
bool rt_oneapi_is_available(void) { return false; }
int64_t rt_oneapi_device_count(void) { return 0; }
int64_t rt_oneapi_malloc_device(int64_t size) { (void)size; return -3; }
bool rt_oneapi_free(int64_t ptr) { (void)ptr; return false; }
bool rt_oneapi_memset(int64_t ptr, int64_t value, int64_t size) {
    (void)ptr; (void)value; (void)size;
    return false;
}
int64_t rt_oneapi_compile_spirv(int64_t bytes, int64_t size) {
    (void)bytes; (void)size;
    return -3;
}
int64_t rt_oneapi_compile_opencl(int64_t source) { (void)source; return -3; }
int64_t rt_oneapi_get_function(int64_t module, int64_t name) {
    (void)module; (void)name;
    return -3;
}
int64_t rt_oneapi_create_queue(void) { return -3; }
bool rt_oneapi_destroy_queue(int64_t queue) { (void)queue; return false; }
bool rt_oneapi_submit_kernel(int64_t queue, int64_t kernel,
                              int64_t global_range, int64_t local_range) {
    (void)queue; (void)kernel; (void)global_range; (void)local_range;
    return false;
}

/* OpenGL */
int64_t rt_opengl_init(int64_t width, int64_t height) {
    (void)width; (void)height;
    return -3;
}
bool rt_opengl_destroy(int64_t ctx) { (void)ctx; return false; }
int64_t rt_opengl_is_available(void) { return 0; }
int64_t rt_opengl_create_fbo(int64_t ctx, int64_t width, int64_t height) {
    (void)ctx; (void)width; (void)height;
    return -3;
}
bool rt_opengl_destroy_fbo(int64_t ctx, int64_t fbo) {
    (void)ctx; (void)fbo;
    return false;
}
bool rt_opengl_bind_fbo(int64_t ctx, int64_t fbo) {
    (void)ctx; (void)fbo;
    return false;
}
bool rt_opengl_clear(int64_t ctx, int64_t color) {
    (void)ctx; (void)color;
    return false;
}
bool rt_opengl_draw_image(int64_t ctx, int64_t x, int64_t y, int64_t width,
                          int64_t height, int64_t pixels, int64_t image_width,
                          int64_t image_height) {
    (void)ctx; (void)x; (void)y; (void)width; (void)height;
    (void)pixels; (void)image_width; (void)image_height;
    return false;
}

/* Intel Engine2D */
bool rt_intel_engine2d_set_args_blit(int64_t fb, int64_t src, int64_t x,
                                     int64_t y, int64_t width, int64_t height,
                                     int64_t fb_width, int64_t fb_height) {
    (void)fb; (void)src; (void)x; (void)y; (void)width; (void)height;
    (void)fb_width; (void)fb_height;
    return false;
}
int64_t rt_intel_engine2d_upload_pixels(int64_t dst, int64_t pixels, int64_t count) {
    (void)dst; (void)pixels; (void)count;
    return -3;
}
int64_t rt_intel_engine2d_upload_host_buf(int64_t dst, int64_t host_buf, int64_t byte_size) {
    (void)dst; (void)host_buf; (void)byte_size;
    return -3;
}
int64_t rt_intel_engine2d_download_pixels(int64_t src, int64_t pixels, int64_t byte_size) {
    (void)src; (void)pixels; (void)byte_size;
    return -3;
}
bool rt_intel_engine2d_set_args_clear(int64_t fb, int64_t color, int64_t width, int64_t height) {
    (void)fb; (void)color; (void)width; (void)height;
    return false;
}
bool rt_intel_engine2d_set_args_rect(int64_t fb, int64_t x, int64_t y, int64_t w, int64_t h,
                                     int64_t color, int64_t fb_w, int64_t fb_h, int64_t filled) {
    (void)fb; (void)x; (void)y; (void)w; (void)h;
    (void)color; (void)fb_w; (void)fb_h; (void)filled;
    return false;
}
bool rt_intel_engine2d_set_args_line(int64_t fb, int64_t x1, int64_t y1, int64_t x2, int64_t y2,
                                     int64_t color, int64_t thickness, int64_t fb_w, int64_t fb_h) {
    (void)fb; (void)x1; (void)y1; (void)x2; (void)y2;
    (void)color; (void)thickness; (void)fb_w; (void)fb_h;
    return false;
}
bool rt_intel_engine2d_set_args_circle(int64_t fb, int64_t cx, int64_t cy, int64_t r,
                                       int64_t color, int64_t fb_w, int64_t fb_h, int64_t filled) {
    (void)fb; (void)cx; (void)cy; (void)r;
    (void)color; (void)fb_w; (void)fb_h; (void)filled;
    return false;
}
bool rt_intel_engine2d_set_args_rounded_rect(int64_t fb, int64_t x, int64_t y, int64_t w, int64_t h,
                                             int64_t radius, int64_t color, int64_t fb_w, int64_t fb_h) {
    (void)fb; (void)x; (void)y; (void)w; (void)h;
    (void)radius; (void)color; (void)fb_w; (void)fb_h;
    return false;
}
bool rt_intel_engine2d_set_args_triangle(int64_t fb, int64_t x1, int64_t y1, int64_t x2, int64_t y2,
                                         int64_t x3, int64_t y3, int64_t color, int64_t fb_w,
                                         int64_t fb_h, int64_t min_x, int64_t min_y) {
    (void)fb; (void)x1; (void)y1; (void)x2; (void)y2;
    (void)x3; (void)y3; (void)color; (void)fb_w;
    (void)fb_h; (void)min_x; (void)min_y;
    return false;
}
bool rt_intel_engine2d_set_args_gradient(int64_t fb, int64_t x, int64_t y, int64_t w, int64_t h,
                                         int64_t top_color, int64_t bottom_color, int64_t fb_w,
                                         int64_t fb_h) {
    (void)fb; (void)x; (void)y; (void)w; (void)h;
    (void)top_color; (void)bottom_color; (void)fb_w; (void)fb_h;
    return false;
}

/* oneAPI backfill (extern decls added .spl-side; unavailable in core C runtime). */
bool rt_oneapi_queue_wait(int64_t queue) { (void)queue; return false; }
bool rt_oneapi_unload_module(int64_t module) { (void)module; return false; }

/* OpenGL backfill (unavailable in core C runtime; fail closed like the block above). */
bool rt_opengl_clear_scissor(int64_t ctx) { (void)ctx; return false; }
bool rt_opengl_set_scissor(int64_t ctx, int64_t x, int64_t y, int64_t w, int64_t h) {
    (void)ctx; (void)x; (void)y; (void)w; (void)h;
    return false;
}
bool rt_opengl_draw_rect(int64_t ctx, int64_t x, int64_t y, int64_t w, int64_t h,
                         int64_t color, int64_t filled) {
    (void)ctx; (void)x; (void)y; (void)w; (void)h; (void)color; (void)filled;
    return false;
}
bool rt_opengl_draw_rounded_rect(int64_t ctx, int64_t x, int64_t y, int64_t w, int64_t h,
                                 int64_t radius, int64_t color) {
    (void)ctx; (void)x; (void)y; (void)w; (void)h; (void)radius; (void)color;
    return false;
}
bool rt_opengl_draw_gradient_rect(int64_t ctx, int64_t x, int64_t y, int64_t w, int64_t h,
                                  int64_t top_color, int64_t bottom_color) {
    (void)ctx; (void)x; (void)y; (void)w; (void)h; (void)top_color; (void)bottom_color;
    return false;
}
bool rt_opengl_draw_line(int64_t ctx, int64_t x1, int64_t y1, int64_t x2, int64_t y2,
                         int64_t color, int64_t thickness) {
    (void)ctx; (void)x1; (void)y1; (void)x2; (void)y2; (void)color; (void)thickness;
    return false;
}
bool rt_opengl_draw_circle(int64_t ctx, int64_t cx, int64_t cy, int64_t radius,
                           int64_t color, int64_t filled) {
    (void)ctx; (void)cx; (void)cy; (void)radius; (void)color; (void)filled;
    return false;
}
bool rt_opengl_draw_triangle(int64_t ctx, int64_t x1, int64_t y1, int64_t x2, int64_t y2,
                             int64_t x3, int64_t y3, int64_t color) {
    (void)ctx; (void)x1; (void)y1; (void)x2; (void)y2; (void)x3; (void)y3; (void)color;
    return false;
}
bool rt_opengl_flush(int64_t ctx) { (void)ctx; return false; }
bool rt_opengl_read_pixels(int64_t ctx, int64_t pixels, int64_t width, int64_t height) {
    (void)ctx; (void)pixels; (void)width; (void)height;
    return false;
}

/* WebGPU backfill (hosted wgpu backend lives in the Rust runtime only). */
bool rt_webgpu_is_available(void) { return false; }
bool rt_webgpu_init(void) { return false; }
int64_t rt_webgpu_create_surface(int32_t width, int32_t height) {
    (void)width; (void)height;
    return 0;
}

/* Real POSIX fd helpers (mirror interpreter_extern/qmp_socket.rs semantics). */
int64_t rt_fd_write(int64_t fd, const char* data, int64_t len) {
#if defined(_WIN32)
    (void)fd; (void)data; (void)len;
    return -1;
#else
    if (fd < 0 || !data || len < 0) return -1;
    ssize_t written = 0;
    while (written < (ssize_t)len) {
        ssize_t n = write((int)fd, data + written, (size_t)(len - written));
        if (n <= 0) return written > 0 ? (int64_t)written : -1;
        written += n;
    }
    return (int64_t)written;
#endif
}
const char* rt_fd_read_until(int64_t fd, uint8_t stop_byte, int64_t max) {
#if defined(_WIN32)
    (void)fd; (void)stop_byte; (void)max;
    return "";
#else
    if (fd < 0 || max <= 0) return "";
    char* buf = (char*)malloc((size_t)max + 1);
    if (!buf) return "";
    int64_t count = 0;
    while (count < max) {
        char ch = 0;
        ssize_t n = read((int)fd, &ch, 1);
        if (n <= 0) break;
        buf[count++] = ch;
        if ((unsigned char)ch == stop_byte) break;
    }
    buf[count] = '\0';
    return buf;
#endif
}
bool rt_fd_close(int64_t fd) {
#if defined(_WIN32)
    (void)fd;
    return false;
#else
    if (fd < 0) return false;
    return close((int)fd) == 0;
#endif
}

/* Hosted SDL2 compositor surface. The title is unused while unavailable. */
SPL_HOSTED_UNAVAILABLE_WEAK int64_t rt_sdl2_init(void) { return 0; }
SPL_HOSTED_UNAVAILABLE_WEAK int64_t rt_sdl2_create_window(const char* title,
                                                           int64_t width,
                                                           int64_t height) {
    (void)title; (void)width; (void)height;
    return 0;
}
#if defined(SIMPLE_CORE_C_STANDALONE)
bool rt_is_interpreter_runtime(void) {
    return false;
}

int64_t rt_cli_run_file(int64_t path, int64_t args, uint8_t gc_log, uint8_t gc_off) {
    (void)path; (void)args; (void)gc_log; (void)gc_off;
    fprintf(stderr, "simple: --fork requires hosted interpreter support\n");
    return 1;
}
#endif

#undef SPL_HOSTED_UNAVAILABLE_WEAK

/* Core-C fallbacks. Full hosted builds provide stronger implementations. */
#if defined(__GNUC__) || defined(__clang__)
#define SPL_CORE_C_WEAK __attribute__((weak))
#else
#define SPL_CORE_C_WEAK
#endif

typedef struct RtCoreAtomicInt {
    atomic_int_fast64_t value;
} RtCoreAtomicInt;

SPL_CORE_C_WEAK int64_t rt_atomic_int_new(int64_t initial) {
    RtCoreAtomicInt* value = (RtCoreAtomicInt*)malloc(sizeof(RtCoreAtomicInt));
    if (!value) return 0;
    atomic_init(&value->value, initial);
    return (int64_t)(intptr_t)value;
}

SPL_CORE_C_WEAK int64_t rt_atomic_int_load(int64_t handle) {
    RtCoreAtomicInt* value = (RtCoreAtomicInt*)(intptr_t)handle;
    return value ? atomic_load_explicit(&value->value, memory_order_seq_cst) : 0;
}

SPL_CORE_C_WEAK bool rt_atomic_int_compare_exchange(int64_t handle, int64_t current, int64_t new_value) {
    RtCoreAtomicInt* value = (RtCoreAtomicInt*)(intptr_t)handle;
    return value && atomic_compare_exchange_strong_explicit(
        &value->value, &current, new_value, memory_order_seq_cst, memory_order_seq_cst);
}

/* rt_thread_sleep is NOT defined here.  runtime_thread.c is the canonical
 * OS-thread provider (see native_project/tools.rs: "runtime_thread.c owns both
 * rt_thread_* and rt_pool_*") and is compiled into every archive that also
 * carries this file, including the Stage4 core archive built with
 * -DSIMPLE_CORE_C_STANDALONE=1.  The weak fallback that used to live here was
 * therefore never selected and only made the symbol appear twice in the core
 * archive, tripping the Stage4 SQLite C-provider "must own <symbol> exactly
 * once" contract. */

static volatile sig_atomic_t rt_core_signal_flags[32];
static volatile sig_atomic_t rt_core_atexit_flag;

static void rt_core_signal_handler(int signal_num) {
    if (signal_num >= 0 && signal_num < 32) rt_core_signal_flags[signal_num] = 1;
}

static void rt_core_atexit_handler(void) {
    rt_core_atexit_flag = 1;
}

SPL_CORE_C_WEAK int64_t rt_signal_install(int64_t signal_num) {
    if (signal_num < 0 || signal_num >= 32) return 0;
#if defined(_WIN32)
    return signal((int)signal_num, rt_core_signal_handler) == SIG_ERR ? 0 : 1;
#else
    struct sigaction action;
    memset(&action, 0, sizeof(action));
    action.sa_handler = rt_core_signal_handler;
    sigemptyset(&action.sa_mask);
    action.sa_flags = SA_RESTART;
    return sigaction((int)signal_num, &action, NULL) == 0 ? 1 : 0;
#endif
}

SPL_CORE_C_WEAK int64_t rt_signal_check(int64_t signal_num) {
    if (signal_num < 0 || signal_num >= 32 || !rt_core_signal_flags[signal_num]) return 0;
    rt_core_signal_flags[signal_num] = 0;
    return 1;
}

SPL_CORE_C_WEAK int64_t rt_atexit_install(void) {
    static int installed;
    if (!installed && atexit(rt_core_atexit_handler) != 0) return 0;
    installed = 1;
    return 1;
}

SPL_CORE_C_WEAK int64_t rt_atexit_check(void) {
    if (!rt_core_atexit_flag) return 0;
    rt_core_atexit_flag = 0;
    return 1;
}

#undef SPL_CORE_C_WEAK

static int64_t rt_host_gpu_queue_now_us(void) {
    struct timespec ts;
#if defined(_WIN32)
    if (timespec_get(&ts, TIME_UTC) == 0) {
        return 0;
    }
#else
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) {
        return 0;
    }
#endif
    return ((int64_t)ts.tv_sec * 1000000) + ((int64_t)ts.tv_nsec / 1000);
}

int64_t rt_host_gpu_lane_event(int64_t lane_code, int64_t phase_code) {
    if ((lane_code != RT_HOST_GPU_LANE_HOST && lane_code != RT_HOST_GPU_LANE_GPU) ||
        (phase_code != RT_HOST_GPU_PHASE_BEGIN && phase_code != RT_HOST_GPU_PHASE_END)) {
        return 0;
    }
    rt_host_gpu_lane_event_total += 1;
    if (phase_code == RT_HOST_GPU_PHASE_BEGIN) {
        rt_host_gpu_lane_begin_total += 1;
    } else {
        rt_host_gpu_lane_end_total += 1;
    }
    rt_host_gpu_lane_last_lane_code = lane_code;
    rt_host_gpu_lane_last_phase_code = phase_code;
    return 1;
}

void rt_host_gpu_lane_reset(void) {
    rt_host_gpu_lane_event_total = 0;
    rt_host_gpu_lane_begin_total = 0;
    rt_host_gpu_lane_end_total = 0;
    rt_host_gpu_lane_last_lane_code = 0;
    rt_host_gpu_lane_last_phase_code = 0;
    rt_host_gpu_queue_reset();
}

int64_t rt_host_gpu_lane_event_count(void) { return rt_host_gpu_lane_event_total; }
int64_t rt_host_gpu_lane_begin_count(void) { return rt_host_gpu_lane_begin_total; }
int64_t rt_host_gpu_lane_end_count(void) { return rt_host_gpu_lane_end_total; }
int64_t rt_host_gpu_lane_last_lane(void) { return rt_host_gpu_lane_last_lane_code; }
int64_t rt_host_gpu_lane_last_phase(void) { return rt_host_gpu_lane_last_phase_code; }

void rt_host_gpu_queue_reset(void) {
    rt_host_gpu_queue_next_packet_id = 1;
    rt_host_gpu_queue_head = 0;
    rt_host_gpu_queue_depth = 0;
    rt_host_gpu_queue_in_flight_head = 0;
    rt_host_gpu_queue_in_flight_depth = 0;
    rt_host_gpu_queue_packet_total = 0;
    rt_host_gpu_queue_submitted_total = 0;
    rt_host_gpu_queue_completed_total = 0;
    rt_host_gpu_queue_last_status_code = RT_HOST_GPU_QUEUE_STATUS_EMPTY;
    rt_host_gpu_queue_last_backend_handle_value = 0;
    rt_host_gpu_queue_last_payload_size_value = 0;
    rt_host_gpu_queue_last_payload_hash_value = 0;
    rt_host_gpu_queue_last_device_time_us_value = 0;
    rt_host_gpu_queue_last_payload_text_value[0] = '\0';
}

static void rt_host_gpu_queue_copy_payload_text(char* dst, const char* src) {
    if (!dst) return;
    if (!src) {
        dst[0] = '\0';
        return;
    }
    strncpy(dst, src, 4095);
    dst[4095] = '\0';
}

int64_t rt_host_gpu_queue_emit_payload_text(int64_t lane_code, int64_t kind_code, int64_t payload_size, int64_t backend_handle, int64_t payload_hash, const char* payload_text) {
    if ((lane_code != RT_HOST_GPU_LANE_HOST && lane_code != RT_HOST_GPU_LANE_GPU) ||
        kind_code < 0 || payload_size < 0 || backend_handle < 0) {
        return 0;
    }
    if (rt_host_gpu_queue_depth + rt_host_gpu_queue_in_flight_depth >= RT_HOST_GPU_QUEUE_CAPACITY) {
        return 0;
    }
    int64_t packet_id = rt_host_gpu_queue_next_packet_id++;
    int64_t tail = (rt_host_gpu_queue_head + rt_host_gpu_queue_depth) % RT_HOST_GPU_QUEUE_CAPACITY;
    rt_host_gpu_queue_lane_codes[tail] = lane_code;
    rt_host_gpu_queue_backend_handles[tail] = backend_handle;
    rt_host_gpu_queue_payload_sizes[tail] = payload_size;
    rt_host_gpu_queue_payload_hashes[tail] = payload_hash;
    rt_host_gpu_queue_copy_payload_text(rt_host_gpu_queue_payload_texts[tail], payload_text);
    rt_host_gpu_queue_depth += 1;
    rt_host_gpu_queue_packet_total += 1;
    rt_host_gpu_queue_last_status_code = RT_HOST_GPU_QUEUE_STATUS_QUEUED;
    return packet_id;
}

int64_t rt_host_gpu_queue_emit_payload(int64_t lane_code, int64_t kind_code, int64_t payload_size, int64_t backend_handle, int64_t payload_hash) {
    return rt_host_gpu_queue_emit_payload_text(lane_code, kind_code, payload_size, backend_handle, payload_hash, "");
}

int64_t rt_host_gpu_queue_emit(int64_t lane_code, int64_t kind_code, int64_t payload_size, int64_t backend_handle) {
    return rt_host_gpu_queue_emit_payload_text(lane_code, kind_code, payload_size, backend_handle, 0, "");
}

int64_t rt_host_gpu_queue_submit(int64_t max_packets) {
    if (max_packets <= 0 || rt_host_gpu_queue_depth <= 0) return 0;
    int64_t submitted = 0;
    while (submitted < max_packets && rt_host_gpu_queue_depth > 0) {
        int64_t source = rt_host_gpu_queue_head;
        int64_t lane_code = rt_host_gpu_queue_lane_codes[source];
        int64_t backend_handle = rt_host_gpu_queue_backend_handles[source];
        rt_host_gpu_queue_head = (rt_host_gpu_queue_head + 1) % RT_HOST_GPU_QUEUE_CAPACITY;
        rt_host_gpu_queue_depth -= 1;
        int64_t tail = (rt_host_gpu_queue_in_flight_head + rt_host_gpu_queue_in_flight_depth) % RT_HOST_GPU_QUEUE_CAPACITY;
        rt_host_gpu_queue_in_flight_lane_codes[tail] = lane_code;
        rt_host_gpu_queue_in_flight_backend_handles[tail] = backend_handle;
        rt_host_gpu_queue_in_flight_payload_sizes[tail] = rt_host_gpu_queue_payload_sizes[source];
        rt_host_gpu_queue_in_flight_payload_hashes[tail] = rt_host_gpu_queue_payload_hashes[source];
        rt_host_gpu_queue_in_flight_submitted_at_us[tail] = rt_host_gpu_queue_now_us();
        rt_host_gpu_queue_copy_payload_text(rt_host_gpu_queue_in_flight_payload_texts[tail], rt_host_gpu_queue_payload_texts[source]);
        rt_host_gpu_queue_in_flight_depth += 1;
        rt_host_gpu_queue_submitted_total += 1;
        rt_host_gpu_queue_last_status_code = RT_HOST_GPU_QUEUE_STATUS_SUBMITTED;
        rt_host_gpu_queue_last_backend_handle_value = backend_handle;
        submitted += 1;
    }
    return submitted;
}

static void rt_host_gpu_queue_complete_packet(int64_t lane_code, int64_t backend_handle, int64_t payload_size, int64_t payload_hash, const char* payload_text, int64_t submitted_at_us) {
    int64_t completed_at_us = rt_host_gpu_queue_now_us();
    rt_host_gpu_queue_last_backend_handle_value = backend_handle;
    rt_host_gpu_queue_last_payload_size_value = payload_size;
    rt_host_gpu_queue_last_payload_hash_value = payload_hash;
    rt_host_gpu_queue_copy_payload_text(rt_host_gpu_queue_last_payload_text_value, payload_text);
    if (lane_code == RT_HOST_GPU_LANE_GPU && backend_handle > 0 && submitted_at_us > 0 && completed_at_us > submitted_at_us) {
        rt_host_gpu_queue_last_device_time_us_value = completed_at_us - submitted_at_us;
    } else if (lane_code == RT_HOST_GPU_LANE_GPU && backend_handle > 0) {
        rt_host_gpu_queue_last_device_time_us_value = 1;
    } else {
        rt_host_gpu_queue_last_device_time_us_value = 0;
    }
    rt_host_gpu_queue_completed_total += 1;
    rt_host_gpu_queue_last_status_code =
        (lane_code == RT_HOST_GPU_LANE_GPU && backend_handle == 0)
        ? RT_HOST_GPU_QUEUE_STATUS_UNAVAILABLE
        : RT_HOST_GPU_QUEUE_STATUS_COMPLETED;
}

int64_t rt_host_gpu_queue_complete(int64_t max_packets) {
    if (max_packets <= 0 || rt_host_gpu_queue_in_flight_depth <= 0) return 0;
    int64_t completed = 0;
    while (completed < max_packets && rt_host_gpu_queue_in_flight_depth > 0) {
        int64_t lane_code = rt_host_gpu_queue_in_flight_lane_codes[rt_host_gpu_queue_in_flight_head];
        int64_t backend_handle = rt_host_gpu_queue_in_flight_backend_handles[rt_host_gpu_queue_in_flight_head];
        int64_t payload_size = rt_host_gpu_queue_in_flight_payload_sizes[rt_host_gpu_queue_in_flight_head];
        int64_t payload_hash = rt_host_gpu_queue_in_flight_payload_hashes[rt_host_gpu_queue_in_flight_head];
        int64_t submitted_at_us = rt_host_gpu_queue_in_flight_submitted_at_us[rt_host_gpu_queue_in_flight_head];
        const char* payload_text = rt_host_gpu_queue_in_flight_payload_texts[rt_host_gpu_queue_in_flight_head];
        rt_host_gpu_queue_in_flight_head = (rt_host_gpu_queue_in_flight_head + 1) % RT_HOST_GPU_QUEUE_CAPACITY;
        rt_host_gpu_queue_in_flight_depth -= 1;
        rt_host_gpu_queue_complete_packet(lane_code, backend_handle, payload_size, payload_hash, payload_text, submitted_at_us);
        completed += 1;
    }
    return completed;
}

int64_t rt_host_gpu_queue_drain(int64_t max_packets) {
    if (max_packets <= 0 || (rt_host_gpu_queue_depth <= 0 && rt_host_gpu_queue_in_flight_depth <= 0)) return 0;
    int64_t drained = 0;
    while (drained < max_packets) {
        if (rt_host_gpu_queue_in_flight_depth > 0) {
            int64_t lane_code = rt_host_gpu_queue_in_flight_lane_codes[rt_host_gpu_queue_in_flight_head];
            int64_t backend_handle = rt_host_gpu_queue_in_flight_backend_handles[rt_host_gpu_queue_in_flight_head];
            int64_t payload_size = rt_host_gpu_queue_in_flight_payload_sizes[rt_host_gpu_queue_in_flight_head];
            int64_t payload_hash = rt_host_gpu_queue_in_flight_payload_hashes[rt_host_gpu_queue_in_flight_head];
            int64_t submitted_at_us = rt_host_gpu_queue_in_flight_submitted_at_us[rt_host_gpu_queue_in_flight_head];
            const char* payload_text = rt_host_gpu_queue_in_flight_payload_texts[rt_host_gpu_queue_in_flight_head];
            rt_host_gpu_queue_in_flight_head = (rt_host_gpu_queue_in_flight_head + 1) % RT_HOST_GPU_QUEUE_CAPACITY;
            rt_host_gpu_queue_in_flight_depth -= 1;
            rt_host_gpu_queue_complete_packet(lane_code, backend_handle, payload_size, payload_hash, payload_text, submitted_at_us);
            drained += 1;
            continue;
        }
        if (rt_host_gpu_queue_depth <= 0) break;
        int64_t lane_code = rt_host_gpu_queue_lane_codes[rt_host_gpu_queue_head];
        int64_t backend_handle = rt_host_gpu_queue_backend_handles[rt_host_gpu_queue_head];
        int64_t payload_size = rt_host_gpu_queue_payload_sizes[rt_host_gpu_queue_head];
        int64_t payload_hash = rt_host_gpu_queue_payload_hashes[rt_host_gpu_queue_head];
        const char* payload_text = rt_host_gpu_queue_payload_texts[rt_host_gpu_queue_head];
        rt_host_gpu_queue_head = (rt_host_gpu_queue_head + 1) % RT_HOST_GPU_QUEUE_CAPACITY;
        rt_host_gpu_queue_depth -= 1;
        rt_host_gpu_queue_submitted_total += 1;
        rt_host_gpu_queue_last_status_code = RT_HOST_GPU_QUEUE_STATUS_SUBMITTED;
        rt_host_gpu_queue_last_backend_handle_value = backend_handle;
        rt_host_gpu_queue_last_payload_size_value = payload_size;
        rt_host_gpu_queue_last_payload_hash_value = payload_hash;
        rt_host_gpu_queue_copy_payload_text(rt_host_gpu_queue_last_payload_text_value, payload_text);
        rt_host_gpu_queue_last_device_time_us_value =
            (lane_code == RT_HOST_GPU_LANE_GPU && backend_handle > 0) ? 1 : 0;
        rt_host_gpu_queue_completed_total += 1;
        rt_host_gpu_queue_last_status_code =
            (lane_code == RT_HOST_GPU_LANE_GPU && backend_handle == 0)
            ? RT_HOST_GPU_QUEUE_STATUS_UNAVAILABLE
            : RT_HOST_GPU_QUEUE_STATUS_COMPLETED;
        drained += 1;
    }
    return drained;
}

int64_t rt_host_gpu_queue_packet_count(void) { return rt_host_gpu_queue_packet_total; }
int64_t rt_host_gpu_queue_submitted_count(void) { return rt_host_gpu_queue_submitted_total; }
int64_t rt_host_gpu_queue_completed_count(void) { return rt_host_gpu_queue_completed_total; }
int64_t rt_host_gpu_queue_in_flight_count(void) { return rt_host_gpu_queue_in_flight_depth; }
int64_t rt_host_gpu_queue_last_status(void) { return rt_host_gpu_queue_last_status_code; }
int64_t rt_host_gpu_queue_last_backend_handle(void) { return rt_host_gpu_queue_last_backend_handle_value; }
int64_t rt_host_gpu_queue_last_device_time_us(void) { return rt_host_gpu_queue_last_device_time_us_value; }
int64_t rt_host_gpu_queue_last_payload_size(void) { return rt_host_gpu_queue_last_payload_size_value; }
int64_t rt_host_gpu_queue_last_payload_hash(void) { return rt_host_gpu_queue_last_payload_hash_value; }
/* Raw form, for in-C callers. */
/* Both Simple declarations spell this `-> text` and RuntimeFuncSpec
 * (runtime_sffi.rs:1058) spells it `&[I64]` -- a RuntimeValue. Returning the
 * static `char*` handed the caller an UNTAGGED word. MEASURED 2026-08-10 as
 * tag=0 through the compiler's emitted ABI in all three C link orders; same
 * defect class as rt_file_read_text. rt_string_new is defined below in this
 * same TU. */
int64_t rt_host_gpu_queue_last_payload_text(void) {
    const char* raw = rt_host_gpu_queue_last_payload_text_value;
    return rt_string_new((const uint8_t*)raw, (uint64_t)strlen(raw));
}

/* RT_CORE_STRING_FLAG_SHARED marks a string owned by a process-wide cache
 * (rt_core_short_string_cache or rt_literal_intern_table). Those objects are
 * handed out repeatedly to unrelated callers, so freeing one corrupts every
 * other holder. rt_string_free refuses them. Stored in the existing padding
 * field, so the struct layout is unchanged. */
#define RT_CORE_STRING_FLAG_SHARED 1u
/* Ordinary strings created before a transient scope is paused are owned by
 * that scope.  Keep this in the existing reserved word so the native string
 * layout and every data offset remain unchanged. */
#define RT_CORE_STRING_FLAG_TRANSIENT 2u

typedef struct RtCoreString {
    uint32_t kind;
    uint32_t reserved; /* RT_CORE_STRING_FLAG_* */
    uint64_t len;
    char data[];
} RtCoreString;

typedef struct RtCoreArray {
    uint8_t kind;
    uint8_t flags;
    uint16_t reserved;
    uint32_t transient_scope_id;
    int64_t len;
    int64_t cap;
    void* data;
} RtCoreArray;

typedef struct RtCoreMutex {
    uint8_t kind;
    uint8_t reserved[7];
    atomic_flag lock;
    int64_t value;
} RtCoreMutex;

typedef struct RtCoreEnum {
    uint8_t kind;
    uint8_t reserved[3];
    uint32_t transient_scope_id;
    uint32_t enum_id;
    uint32_t discriminant;
    uint32_t reserved2;
    int64_t payload;
} RtCoreEnum;

typedef struct RtCoreClosure {
    uint8_t kind;
    uint8_t reserved[3];
    uint32_t transient_scope_id;
    int64_t func_ptr;
    int64_t capture_count;
    int64_t captures[];
} RtCoreClosure;

/* RtCore-native dictionary: open-addressing hash table over the tagged-int64
 * value representation. Keys and values are stored as tagged RtCore values, so
 * int keys (e.g. Dict<i64,V>) and string keys both work natively — unlike the
 * legacy string-only SplDict. Detected via the `kind` first byte (mirrors
 * RtCoreArray) so rt_index_get/rt_index_set/rt_contains can tag-dispatch. */
typedef struct RtCoreDictEntry {
    int64_t key;       /* canonicalized tagged key */
    int64_t value;     /* tagged value */
    uint64_t hash;
    int8_t occupied;   /* 0 = empty, 1 = live, -1 = tombstone */
} RtCoreDictEntry;

typedef struct RtCoreDict {
    uint8_t kind;      /* RT_VALUE_HEAP_DICT */
    uint8_t flags;
    uint16_t reserved;
    uint32_t transient_scope_id;
    int64_t cap;       /* power of two */
    int64_t len;       /* live entries */
    int64_t tombstones;
    RtCoreDictEntry* entries;
} RtCoreDict;

/* Heap-boxed f64 (see RT_VALUE_HEAP_FLOAT). A leaf object: the full double is
 * stored verbatim so container/Any floats round-trip exactly. Discrimination is
 * O(1): the pointer is validated against rt_core_float_registry (a HashSet
 * membership test performed BEFORE any ->value/->kind dereference), so a stray
 * i64 that merely aliases TAG_HEAP is never dereferenced. */
typedef struct RtCoreFloat {
    uint32_t kind;      /* RT_VALUE_HEAP_FLOAT */
    uint32_t transient_scope_id;
    double value;
} RtCoreFloat;

/* Heap-boxed wide integer (see RT_VALUE_HEAP_INT). Same layout as RtCoreFloat
 * (kind, transient_scope_id, 8-byte payload) so it shares every lifecycle path. */
typedef struct RtCoreWideInt {
    uint32_t kind;      /* RT_VALUE_HEAP_INT */
    uint32_t transient_scope_id;
    int64_t value;
} RtCoreWideInt;

/* Heap-boxed unsigned wide integer (see RT_VALUE_HEAP_UINT). Same layout as
 * RtCoreFloat/RtCoreWideInt (kind, transient_scope_id, 8-byte payload) so it
 * shares every lifecycle path; the payload is UNSIGNED because every consumer
 * compares it as such (`u->value == (uint64_t)expected`,
 * `u->value <= (uint64_t)(INT64_MAX >> 3)`). */
typedef struct RtCoreUInt {
    uint32_t kind;      /* RT_VALUE_HEAP_UINT */
    uint32_t transient_scope_id;
    uint64_t value;
} RtCoreUInt;

static RtCoreDict* rt_core_as_dict(int64_t value);
static int64_t rt_core_dict_lookup(RtCoreDict* d, int64_t key);
static int rt_core_dict_put(RtCoreDict* d, int64_t key, int64_t value);
static int rt_core_dict_has(RtCoreDict* d, int64_t key);
static int rt_core_dict_del(RtCoreDict* d, int64_t key);

static _Atomic size_t rt_core_heap_registry_count = 0;
static RtCoreString* rt_core_short_string_cache[257] = {0};
static atomic_flag rt_core_short_string_cache_lock = ATOMIC_FLAG_INIT;
static _Atomic uint32_t rt_core_transient_array_scope_next_id = 1;
static _Thread_local uint32_t rt_core_transient_array_scope_id = 0;
static _Thread_local int rt_core_transient_array_scope_active = 0;
static _Thread_local int rt_core_transient_array_scope_paused = 0;
static _Thread_local void** rt_core_transient_heap_scope_objects = NULL;
static _Thread_local size_t rt_core_transient_heap_scope_object_len = 0;
static _Thread_local size_t rt_core_transient_heap_scope_object_cap = 0;
typedef struct RtCoreTransientRawAlloc {
    uintptr_t ptr;
    size_t bytes;
} RtCoreTransientRawAlloc;
static _Thread_local RtCoreTransientRawAlloc* rt_core_transient_raw_allocs = NULL;
static _Thread_local size_t rt_core_transient_raw_alloc_cap = 0;
static _Thread_local size_t rt_core_transient_raw_alloc_len = 0;
static _Thread_local size_t rt_core_transient_raw_alloc_tombs = 0;
static RtCoreMutex** rt_core_mutex_registry = NULL;
static size_t rt_core_mutex_registry_len = 0;
static size_t rt_core_mutex_registry_cap = 0;
static atomic_flag rt_core_mutex_registry_lock = ATOMIC_FLAG_INIT;

static int rt_core_register_immortal_ptr(void* ptr);
static int rt_core_is_registered_immortal_ptr(void* ptr);
static int rt_core_unregister_immortal_ptr(void* ptr);
static void rt_core_reclaim_transient_immortal(uint32_t scope_id);
static void rt_core_reclaim_transient_raw(void);
static atomic_flag rt_core_heap_lifecycle_lock = ATOMIC_FLAG_INIT;

static void rt_core_heap_lifecycle_acquire(void) {
    while (atomic_flag_test_and_set_explicit(
        &rt_core_heap_lifecycle_lock, memory_order_acquire)) {}
}

static void rt_core_heap_lifecycle_release(void) {
    atomic_flag_clear_explicit(&rt_core_heap_lifecycle_lock, memory_order_release);
}

static uint32_t rt_core_registered_object_kind(void* ptr) {
    uint32_t wide_kind = *(uint32_t*)ptr;
    if (wide_kind == RT_VALUE_HEAP_STRING || wide_kind == RT_VALUE_HEAP_FLOAT ||
        wide_kind == RT_VALUE_HEAP_INT || wide_kind == RT_VALUE_HEAP_UINT) {
        return wide_kind;
    }
    return *(uint8_t*)ptr;
}

static uint32_t rt_core_transient_scope_for_new_object(void) {
    return rt_core_transient_array_scope_active && !rt_core_transient_array_scope_paused
        ? rt_core_transient_array_scope_id
        : 0;
}

#define RT_CORE_TRANSIENT_SCOPE_MAX_OBJECTS ((size_t)1 << 24)

static int rt_core_track_transient_immortal(void* ptr) {
    if (rt_core_transient_heap_scope_object_len == rt_core_transient_heap_scope_object_cap) {
        size_t next_cap = rt_core_transient_heap_scope_object_cap == 0
            ? 64
            : rt_core_transient_heap_scope_object_cap * 2;
        if (next_cap > RT_CORE_TRANSIENT_SCOPE_MAX_OBJECTS ||
            next_cap > SIZE_MAX / sizeof(void*)) {
            return 0;
        }
        void** next = (void**)realloc(
            rt_core_transient_heap_scope_objects, next_cap * sizeof(void*));
        if (!next) return 0;
        rt_core_transient_heap_scope_objects = next;
        rt_core_transient_heap_scope_object_cap = next_cap;
    }
    rt_core_transient_heap_scope_objects[rt_core_transient_heap_scope_object_len++] = ptr;
    return 1;
}

static int rt_core_register_scoped_immortal(void* ptr, uint32_t* object_scope_id) {
    *object_scope_id = rt_core_transient_scope_for_new_object();
    if (*object_scope_id && !rt_core_track_transient_immortal(ptr)) return 0;
    if (rt_core_register_immortal_ptr(ptr)) return 1;
    if (*object_scope_id && rt_core_transient_heap_scope_object_len > 0 &&
        rt_core_transient_heap_scope_objects[rt_core_transient_heap_scope_object_len - 1] == ptr) {
        rt_core_transient_heap_scope_object_len--;
    }
    *object_scope_id = 0;
    return 0;
}

static int rt_core_register_string(RtCoreString* s) {
    if (!s) return 0;
    if (rt_core_transient_scope_for_new_object() != 0) {
        s->reserved |= RT_CORE_STRING_FLAG_TRANSIENT;
        if (!rt_core_track_transient_immortal(s)) {
            s->reserved &= ~RT_CORE_STRING_FLAG_TRANSIENT;
            return 0;
        }
        if (rt_core_register_immortal_ptr(s)) return 1;
        if (rt_core_transient_heap_scope_object_len > 0 &&
            rt_core_transient_heap_scope_objects[rt_core_transient_heap_scope_object_len - 1] == s) {
            rt_core_transient_heap_scope_object_len--;
        }
        s->reserved &= ~RT_CORE_STRING_FLAG_TRANSIENT;
        return 0;
    }
    return rt_core_register_immortal_ptr(s);
}

static int rt_core_register_persistent_string(RtCoreString* s) {
    if (!s) return 0;
    s->reserved &= ~RT_CORE_STRING_FLAG_TRANSIENT;
    return rt_core_register_immortal_ptr(s);
}

static int rt_core_is_registered_string(RtCoreString* s) {
    return rt_core_is_registered_immortal_ptr(s);
}

/* RtCoreDict membership, mirroring the string/float registries above.
 *
 * Before this existed, rt_core_as_dict trusted the TAG_HEAP bits alone and read
 * (masked_value)->kind directly. That is the same flaw that produced the enum
 * SIGSEGV documented at rt_core_register_enum below: a flat i64 payload
 * congruent to 1 mod 8 (9, 17, -7, ...) aliases RT_VALUE_TAG_HEAP without being
 * a heap object at all, so the dereference lands on a wild address. Every dict
 * is created at exactly one choke point (rt_dict_new) and registered there, so
 * rt_core_as_dict can now perform a PURE POINTER COMPARISON before touching
 * ->kind. The shared pointer registry is the right backing store; scoped dicts
 * are removed from it when their transient scope ends. */
static int rt_core_register_dict(RtCoreDict* d) {
    return rt_core_register_scoped_immortal(d, &d->transient_scope_id);
}

static int rt_core_is_registered_dict(RtCoreDict* d) {
    return rt_core_is_registered_immortal_ptr(d);
}

static int rt_core_register_array(RtCoreArray* array) {
    if (!array) return 0;
    return rt_core_register_scoped_immortal(array, &array->transient_scope_id);
}

static int rt_core_is_registered_array(RtCoreArray* array) {
    return array && rt_core_is_registered_immortal_ptr(array) &&
        array->kind == RT_VALUE_HEAP_ARRAY;
}

static int rt_core_unregister_array(RtCoreArray* array) {
    return rt_core_unregister_immortal_ptr(array);
}

static int rt_core_register_mutex(RtCoreMutex* mutex) {
    if (!mutex) return 0;
    while (atomic_flag_test_and_set_explicit(&rt_core_mutex_registry_lock, memory_order_acquire)) { }
    if (rt_core_mutex_registry_len == rt_core_mutex_registry_cap) {
        size_t next_cap = rt_core_mutex_registry_cap == 0 ? 16 : rt_core_mutex_registry_cap * 2;
        RtCoreMutex** next = (RtCoreMutex**)realloc(rt_core_mutex_registry, next_cap * sizeof(RtCoreMutex*));
        if (!next) {
            atomic_flag_clear_explicit(&rt_core_mutex_registry_lock, memory_order_release);
            return 0;
        }
        rt_core_mutex_registry = next;
        rt_core_mutex_registry_cap = next_cap;
    }
    rt_core_mutex_registry[rt_core_mutex_registry_len++] = mutex;
    atomic_fetch_add_explicit(&rt_core_heap_registry_count, 1, memory_order_relaxed);
    atomic_flag_clear_explicit(&rt_core_mutex_registry_lock, memory_order_release);
    return 1;
}

static int rt_core_is_registered_mutex(RtCoreMutex* mutex) {
    int found = 0;
    while (atomic_flag_test_and_set_explicit(&rt_core_mutex_registry_lock, memory_order_acquire)) { }
    for (size_t i = 0; i < rt_core_mutex_registry_len; i++) {
        if (rt_core_mutex_registry[i] == mutex) {
            found = 1;
            break;
        }
    }
    atomic_flag_clear_explicit(&rt_core_mutex_registry_lock, memory_order_release);
    return found;
}

/* Bug (native_rt_is_none_heap_tag_collision_segv): a flat (unboxed) i64?/bool?
 * Option payload is passed through as its bare bit pattern -- it is NOT
 * NaN-boxed, so a payload value congruent to 1 mod 8 (9, 17, 25, -7, ...)
 * numerically collides with RT_VALUE_TAG_HEAP (see RT_VALUE_TAG_MASK above).
 * rt_is_none()/rt_enum_discriminant() used to call rt_core_as_enum() on ANY
 * non-nil value to test "is this a boxed None enum", and rt_core_as_enum()
 * trusted the tag bits alone before dereferencing (masked_value)->kind --
 * for payload 9 that dereferences wild address 0x8 and SIGSEGVs. Negative
 * payloads (e.g. -7) additionally wrap to a huge unmapped address under the
 * same flaw, so a plain "low address" guard is not sufficient either.
 *
 * Fix: mirror the string registry above. RtCoreEnum objects are created at
 * exactly one choke point (rt_enum_new) and registered there; rt_core_as_enum
 * now checks registry membership -- a PURE POINTER COMPARISON, no dereference
 * -- before ever reading ->kind. A flat payload that merely aliases the HEAP
 * tag bits is never a member of this registry, so it now resolves to "not an
 * enum" (NULL) instead of being dereferenced. Real heap-boxed enums (Option
 * or otherwise) are unaffected since they are always registered at creation.
 *
 * PERF (native_build_parser_100cps_regression_2026-07-26): the comment above
 * always said "mirror the string registry" but the code below instead kept a
 * flat RtCoreEnum* array scanned linearly on every membership test -- unlike
 * the string/dict/float registries, which already share the O(1) open-
 * addressing hash table (rt_core_register/is_registered_immortal_ptr). Since
 * this registry is NEVER pruned (no unregister_enum exists -- every enum ever
 * boxed for the life of the process stays a member) and Option/Result enums
 * are created continuously by ordinary Simple code (every `if val x = opt`,
 * `?` propagation, etc.), rt_core_is_registered_enum's cost grew with total
 * cumulative enum allocations for the process, not live count. In a
 * long-running process (e.g. native-build parsing hundreds of kernel-closure
 * files in one run) this turned every `rt_is_none`/`rt_enum_discriminant`
 * call -- which is on the hot path of essentially all Option/Result-using
 * code, including the parser's own use of Option -- into an O(n) scan over an
 * ever-growing array, producing per-file parse times that degraded as
 * heap_registry grew into the millions (measured: ~190 chars/sec early in a
 * run collapsing to ~28 chars/sec after 48 files / heap_registry=4.1M). Route
 * through the shared immortal hash table instead, exactly like
 * rt_core_register_dict/rt_core_register_float above, restoring amortized
 * O(1) membership tests. */
static int rt_core_register_enum(RtCoreEnum* e) {
    if (!e) return 0;
    return rt_core_register_scoped_immortal(e, &e->transient_scope_id);
}

static int rt_core_is_registered_enum(RtCoreEnum* e) {
    return rt_core_is_registered_immortal_ptr(e);
}

int64_t rt_heap_registry_count(void) {
    return (int64_t)atomic_load_explicit(&rt_core_heap_registry_count, memory_order_relaxed);
}

int8_t rt_transient_array_scope_begin(void) {
    if (rt_core_transient_array_scope_active || rt_core_transient_heap_scope_object_len != 0 ||
        rt_core_transient_raw_alloc_len != 0) return 0;
    uint32_t next_id =
        atomic_load_explicit(&rt_core_transient_array_scope_next_id, memory_order_relaxed);
    while (next_id != 0) {
        uint32_t successor = next_id == UINT32_MAX ? 0 : next_id + 1;
        if (atomic_compare_exchange_weak_explicit(
                &rt_core_transient_array_scope_next_id, &next_id, successor,
                memory_order_relaxed, memory_order_relaxed)) {
            break;
        }
    }
    if (next_id == 0) return 0;
    rt_core_transient_array_scope_id = next_id;
    rt_core_transient_array_scope_active = 1;
    rt_core_transient_array_scope_paused = 0;
    return 1;
}

int8_t rt_transient_array_scope_pause(void) {
    if (!rt_core_transient_array_scope_active) return 0;
    rt_core_transient_array_scope_paused = 1;
    return 1;
}

int8_t rt_transient_array_scope_end(void) {
    if (!rt_core_transient_array_scope_active) return 0;
    const uint32_t scope_id = rt_core_transient_array_scope_id;
    rt_core_transient_array_scope_active = 0;
    rt_core_transient_array_scope_paused = 0;

    rt_core_reclaim_transient_immortal(scope_id);
    rt_core_reclaim_transient_raw();
    return 1;
}

/* PERF (native_build_parser_100cps_regression_2026-07-26): closures were
 * tracked in a flat RtCoreClosure* array scanned linearly under a spinlock on
 * EVERY closure invocation (rt_core_as_closure), exactly the same O(n) growth
 * pattern as the enum registry above -- closures have no unregister path
 * either (created once at rt_closure_new and immortal for the life of the
 * process), so this table only ever grows and every call site paid for the
 * full cumulative allocation count. Route through the same shared O(1)
 * open-addressing immortal-pointer hash table used by strings/dicts/floats/
 * enums instead of a bespoke array+lock. */
static int rt_core_register_closure(RtCoreClosure* closure) {
    if (!closure) return 0;
    return rt_core_register_scoped_immortal(closure, &closure->transient_scope_id);
}

static RtCoreClosure* rt_core_as_closure(int64_t value) {
    if ((((uint64_t)value) & RT_VALUE_TAG_MASK) != RT_VALUE_TAG_HEAP) return NULL;
    RtCoreClosure* closure = (RtCoreClosure*)(uintptr_t)(((uint64_t)value) & ~RT_VALUE_TAG_MASK);
    if (!closure) return NULL;
    /* Membership is a pointer-only comparison inside
     * rt_core_is_registered_immortal_ptr. Do not dereference a raw function
     * pointer that merely collides with the heap tag. */
    if (!rt_core_is_registered_immortal_ptr(closure)) return NULL;
    return closure->kind == RT_VALUE_HEAP_CLOSURE ? closure : NULL;
}

/* ----------------------------------------------------------------------------
 * Immortal heap-pointer registry (O(1) discrimination).
 *
 * Strings and container floats are numerous, so linear membership scans make
 * compiler workloads O(n^2). This open-addressing HashSet provides O(1)
 * amortized membership. The pointer-only lookup happens before any dereference,
 * so a flat i64 that merely aliases RT_VALUE_TAG_HEAP is rejected safely.
 *
 * Only objects with a leading `kind` field enter this table. Strings remain
 * process-persistent; scoped parser objects are erased before being freed.
 * -------------------------------------------------------------------------- */
/* Open-addressing table. 0 = never used, TOMBSTONE = erased.
 *
 * The table originally had no deletion at all (hence "immortal"), which is why
 * nothing in this runtime could free a string: erasing an entry by writing 0
 * would truncate any probe chain that ran through that slot, making unrelated
 * still-live pointers read as unregistered. Deletion therefore writes a
 * tombstone, which terminates insertion but NOT lookup. Tombstones occupy
 * slots, so they are counted against the load factor and reclaimed on grow. */
#define RT_CORE_IMMORTAL_TOMBSTONE ((uintptr_t)1)

static uintptr_t* rt_core_immortal_registry = NULL; /* open-addressing table, 0 = empty */
static size_t rt_core_immortal_registry_cap = 0;    /* power of two, or 0 */
static size_t rt_core_immortal_registry_len = 0;
static size_t rt_core_immortal_registry_tombs = 0;
static atomic_flag rt_core_immortal_registry_lock = ATOMIC_FLAG_INIT;

static void rt_core_immortal_registry_acquire(void) {
    while (atomic_flag_test_and_set_explicit(&rt_core_immortal_registry_lock, memory_order_acquire)) {}
}
static void rt_core_immortal_registry_release(void) {
    atomic_flag_clear_explicit(&rt_core_immortal_registry_lock, memory_order_release);
}

static inline size_t rt_core_immortal_hash_ptr(uintptr_t p) {
    uint64_t x = (uint64_t)p;
    x ^= x >> 33;
    x *= 0xff51afd7ed558ccdULL;
    x ^= x >> 33;
    return (size_t)x;
}

#define RT_CORE_TRANSIENT_RAW_TOMBSTONE ((uintptr_t)1)
#define RT_CORE_TRANSIENT_RAW_OWNED_BIT ((size_t)1 << (sizeof(size_t) * CHAR_BIT - 1))
#define RT_CORE_TRANSIENT_RAW_SIZE_MASK (~RT_CORE_TRANSIENT_RAW_OWNED_BIT)

static int rt_core_transient_raw_insert_raw(uintptr_t ptr, size_t bytes) {
    size_t mask = rt_core_transient_raw_alloc_cap - 1;
    size_t i = rt_core_immortal_hash_ptr(ptr) & mask;
    size_t first_tomb = SIZE_MAX;
    for (;;) {
        uintptr_t entry = rt_core_transient_raw_allocs[i].ptr;
        if (entry == 0) {
            size_t target = first_tomb == SIZE_MAX ? i : first_tomb;
            rt_core_transient_raw_allocs[target] = (RtCoreTransientRawAlloc){ptr, bytes};
            if (first_tomb != SIZE_MAX) rt_core_transient_raw_alloc_tombs--;
            rt_core_transient_raw_alloc_len++;
            return 1;
        }
        if (entry == RT_CORE_TRANSIENT_RAW_TOMBSTONE) {
            if (first_tomb == SIZE_MAX) first_tomb = i;
        } else if (entry == ptr) {
            rt_core_transient_raw_allocs[i].bytes = bytes;
            return 1;
        }
        i = (i + 1) & mask;
    }
}

static int rt_core_transient_raw_grow(void) {
    size_t next_cap = rt_core_transient_raw_alloc_cap == 0
        ? 256
        : rt_core_transient_raw_alloc_cap * 2;
    if (next_cap > SIZE_MAX / sizeof(RtCoreTransientRawAlloc)) return 0;
    RtCoreTransientRawAlloc* fresh = (RtCoreTransientRawAlloc*)calloc(
        next_cap, sizeof(RtCoreTransientRawAlloc));
    if (!fresh) return 0;
    RtCoreTransientRawAlloc* old = rt_core_transient_raw_allocs;
    size_t old_cap = rt_core_transient_raw_alloc_cap;
    rt_core_transient_raw_allocs = fresh;
    rt_core_transient_raw_alloc_cap = next_cap;
    rt_core_transient_raw_alloc_len = 0;
    rt_core_transient_raw_alloc_tombs = 0;
    for (size_t i = 0; i < old_cap; i++) {
        uintptr_t old_ptr = old[i].ptr;
        if (old_ptr != 0 && old_ptr != RT_CORE_TRANSIENT_RAW_TOMBSTONE) {
            rt_core_transient_raw_insert_raw(old_ptr, old[i].bytes);
        }
    }
    free(old);
    return 1;
}

static int rt_core_transient_raw_register_state(void* ptr, size_t bytes, int owned) {
    if (!ptr || !rt_core_transient_array_scope_active) return ptr != NULL;
    if (bytes > RT_CORE_TRANSIENT_RAW_SIZE_MASK) return 0;
    if ((rt_core_transient_raw_alloc_len + rt_core_transient_raw_alloc_tombs + 1) * 10
            >= rt_core_transient_raw_alloc_cap * 7 && !rt_core_transient_raw_grow()) {
        return 0;
    }
    size_t stored = bytes | (owned ? RT_CORE_TRANSIENT_RAW_OWNED_BIT : 0);
    return rt_core_transient_raw_insert_raw((uintptr_t)ptr, stored);
}

static int rt_core_transient_raw_register(void* ptr, size_t bytes) {
    return rt_core_transient_raw_register_state(
        ptr, bytes, !rt_core_transient_array_scope_paused);
}

static RtCoreTransientRawAlloc* rt_core_transient_raw_lookup(uintptr_t ptr) {
    if (!ptr || rt_core_transient_raw_alloc_cap == 0) return NULL;
    size_t mask = rt_core_transient_raw_alloc_cap - 1;
    size_t i = rt_core_immortal_hash_ptr(ptr) & mask;
    for (;;) {
        uintptr_t entry = rt_core_transient_raw_allocs[i].ptr;
        if (entry == 0) return NULL;
        if (entry == ptr) return &rt_core_transient_raw_allocs[i];
        i = (i + 1) & mask;
    }
}

static void rt_core_transient_raw_erase(void* ptr) {
    RtCoreTransientRawAlloc* entry = rt_core_transient_raw_lookup((uintptr_t)ptr);
    if (!entry) return;
    entry->ptr = RT_CORE_TRANSIENT_RAW_TOMBSTONE;
    entry->bytes = 0;
    rt_core_transient_raw_alloc_len--;
    rt_core_transient_raw_alloc_tombs++;
}

static void rt_core_transient_raw_clear(void) {
    if (rt_core_transient_raw_alloc_cap != 0) {
        memset(rt_core_transient_raw_allocs, 0,
            rt_core_transient_raw_alloc_cap * sizeof(RtCoreTransientRawAlloc));
    }
    rt_core_transient_raw_alloc_len = 0;
    rt_core_transient_raw_alloc_tombs = 0;
}

static void rt_struct_alloc_unregister(void* ptr);

static void rt_core_reclaim_transient_raw(void) {
    for (size_t i = 0; i < rt_core_transient_raw_alloc_cap; i++) {
        RtCoreTransientRawAlloc* entry = &rt_core_transient_raw_allocs[i];
        if (entry->ptr == 0 || entry->ptr == RT_CORE_TRANSIENT_RAW_TOMBSTONE) continue;
        if (entry->bytes & RT_CORE_TRANSIENT_RAW_OWNED_BIT) {
            void* raw = (void*)entry->ptr;
            rt_struct_alloc_unregister(raw);
            /* Now that sampled guard slots are registered here too, reclaim
             * must not hand one to free(): a slot is a page-aligned mmap
             * mapping, not a libc chunk. Route it through the guard's own
             * reclaim, which PROT_NONEs the mapping so a later UAF traps.
             * This mirrors rt_free's guard-slot branch. */
            if (rt_mem_guard_is_slot(raw)) {
                rt_mem_guard_free_sampled(raw);
            } else {
                free(raw);
            }
        }
    }
    rt_core_transient_raw_clear();
}

/* caller holds the lock; table has a free slot */
static int rt_core_immortal_registry_insert_raw(uintptr_t p) {
    size_t mask = rt_core_immortal_registry_cap - 1;
    size_t i = rt_core_immortal_hash_ptr(p) & mask;
    size_t first_tomb = SIZE_MAX;
    for (;;) {
        uintptr_t e = rt_core_immortal_registry[i];
        if (e == 0) {
            /* Reuse the earliest tombstone seen, but only after proving p is
             * not already present further along the probe chain. */
            if (first_tomb != SIZE_MAX) {
                rt_core_immortal_registry[first_tomb] = p;
                rt_core_immortal_registry_tombs--;
            } else {
                rt_core_immortal_registry[i] = p;
            }
            rt_core_immortal_registry_len++;
            return 1;
        }
        if (e == RT_CORE_IMMORTAL_TOMBSTONE) {
            if (first_tomb == SIZE_MAX) first_tomb = i;
        } else if (e == p) {
            return 0;
        }
        i = (i + 1) & mask;
    }
}

/* caller holds the lock; returns 1 if an entry was erased */
static int rt_core_immortal_registry_erase_raw(uintptr_t p) {
    if (rt_core_immortal_registry_cap == 0) return 0;
    size_t mask = rt_core_immortal_registry_cap - 1;
    size_t i = rt_core_immortal_hash_ptr(p) & mask;
    for (;;) {
        uintptr_t e = rt_core_immortal_registry[i];
        if (e == 0) return 0;
        if (e == p) {
            rt_core_immortal_registry[i] = RT_CORE_IMMORTAL_TOMBSTONE;
            rt_core_immortal_registry_len--;
            rt_core_immortal_registry_tombs++;
            return 1;
        }
        i = (i + 1) & mask;
    }
}

/* caller holds the lock */
static int rt_core_immortal_registry_resize(size_t new_cap) {
    if (new_cap > SIZE_MAX / sizeof(uintptr_t)) return 0;
    uintptr_t* fresh = (uintptr_t*)calloc(new_cap, sizeof(uintptr_t));
    if (!fresh) return 0;
    uintptr_t* old = rt_core_immortal_registry;
    size_t old_cap = rt_core_immortal_registry_cap;
    rt_core_immortal_registry = fresh;
    rt_core_immortal_registry_cap = new_cap;
    rt_core_immortal_registry_len = 0;
    rt_core_immortal_registry_tombs = 0; /* rehash drops tombstones */
    for (size_t i = 0; i < old_cap; i++) {
        if (old[i] != 0 && old[i] != RT_CORE_IMMORTAL_TOMBSTONE) {
            rt_core_immortal_registry_insert_raw(old[i]);
        }
    }
    free(old);
    return 1;
}

static int rt_core_register_immortal_ptr(void* ptr) {
    if (!ptr) return 0;
    rt_core_immortal_registry_acquire();
    /* grow at 70% load; tombstones count as occupancy since they lengthen
     * probe chains exactly as live entries do */
    if ((rt_core_immortal_registry_len + rt_core_immortal_registry_tombs + 1) * 10
            >= rt_core_immortal_registry_cap * 7) {
        size_t new_cap = rt_core_immortal_registry_cap == 0 ? 256 : rt_core_immortal_registry_cap * 2;
        /* A transient teardown can leave millions of tombstones while very
         * few live objects remain. Rehash those at the same capacity instead
         * of doubling the table once per source file. */
        if (rt_core_immortal_registry_cap != 0 &&
            rt_core_immortal_registry_tombs > rt_core_immortal_registry_len &&
            (rt_core_immortal_registry_len + 1) * 10 < rt_core_immortal_registry_cap * 5) {
            new_cap = rt_core_immortal_registry_cap;
        }
        if (!rt_core_immortal_registry_resize(new_cap)) {
            rt_core_immortal_registry_release();
            return 0;
        }
    }
    int inserted = rt_core_immortal_registry_insert_raw((uintptr_t)ptr);
    if (inserted) {
        atomic_fetch_add_explicit(&rt_core_heap_registry_count, 1, memory_order_relaxed);
    }
    rt_core_immortal_registry_release();
    return 1;
}

static int rt_core_is_registered_immortal_ptr(void* ptr) {
    if (!ptr) return 0;
    int found = 0;
    rt_core_immortal_registry_acquire();
    if (rt_core_immortal_registry_cap != 0) {
        size_t mask = rt_core_immortal_registry_cap - 1;
        size_t i = rt_core_immortal_hash_ptr((uintptr_t)ptr) & mask;
        for (;;) {
            uintptr_t e = rt_core_immortal_registry[i];
            if (e == 0) break;
            if (e == (uintptr_t)ptr) { found = 1; break; }
            i = (i + 1) & mask;
        }
    }
    rt_core_immortal_registry_release();
    return found;
}

static int rt_core_unregister_immortal_ptr(void* ptr) {
    if (!ptr) return 0;
    rt_core_heap_lifecycle_acquire();
    rt_core_immortal_registry_acquire();
    int erased = rt_core_immortal_registry_erase_raw((uintptr_t)ptr);
    rt_core_immortal_registry_release();
    if (erased) {
        atomic_fetch_sub_explicit(&rt_core_heap_registry_count, 1, memory_order_relaxed);
    }
    rt_core_heap_lifecycle_release();
    return erased;
}

static void rt_core_reclaim_transient_immortal(uint32_t scope_id) {
    rt_core_heap_lifecycle_acquire();
    for (size_t i = 0; i < rt_core_transient_heap_scope_object_len; i++) {
        void* ptr = rt_core_transient_heap_scope_objects[i];
        if (!rt_core_is_registered_immortal_ptr(ptr)) continue;
        uint32_t kind = rt_core_registered_object_kind(ptr);
        uint32_t* object_scope = NULL;
        int reclaim_string = 0;
        switch (kind) {
            case RT_VALUE_HEAP_STRING: {
                RtCoreString* string = (RtCoreString*)ptr;
                reclaim_string =
                    (string->reserved & RT_CORE_STRING_FLAG_TRANSIENT) != 0 &&
                    (string->reserved & RT_CORE_STRING_FLAG_SHARED) == 0;
                break;
            }
            case RT_VALUE_HEAP_ARRAY:
                object_scope = &((RtCoreArray*)ptr)->transient_scope_id;
                break;
            case RT_VALUE_HEAP_DICT:
                object_scope = &((RtCoreDict*)ptr)->transient_scope_id;
                break;
            case RT_VALUE_HEAP_ENUM:
                object_scope = &((RtCoreEnum*)ptr)->transient_scope_id;
                break;
            case RT_VALUE_HEAP_CLOSURE:
                object_scope = &((RtCoreClosure*)ptr)->transient_scope_id;
                break;
            case RT_VALUE_HEAP_FLOAT:
            case RT_VALUE_HEAP_INT:   /* identical leaf layout */
            case RT_VALUE_HEAP_UINT:  /* identical leaf layout */
                object_scope = &((RtCoreFloat*)ptr)->transient_scope_id;
                break;
            default:
                break;
        }
        if (!reclaim_string && (!object_scope || *object_scope != scope_id)) continue;
        rt_core_immortal_registry_acquire();
        int erased = rt_core_immortal_registry_erase_raw((uintptr_t)ptr);
        rt_core_immortal_registry_release();
        if (!erased) continue;
        atomic_fetch_sub_explicit(&rt_core_heap_registry_count, 1, memory_order_relaxed);
        switch (rt_core_registered_object_kind(ptr)) {
            case RT_VALUE_HEAP_ARRAY:
                free(((RtCoreArray*)ptr)->data);
                break;
            case RT_VALUE_HEAP_DICT:
                free(((RtCoreDict*)ptr)->entries);
                break;
            default:
                break;
        }
        free(ptr);
    }
    rt_core_transient_heap_scope_object_len = 0;
    /* String-heavy parses can briefly track millions of pointers. Do not pin
     * that peak-capacity side buffer for the remaining compilation. */
    if (rt_core_transient_heap_scope_object_cap > 262144) {
        free(rt_core_transient_heap_scope_objects);
        rt_core_transient_heap_scope_objects = NULL;
        rt_core_transient_heap_scope_object_cap = 0;
    }
    rt_core_heap_lifecycle_release();
}

static int rt_core_unregister_string(RtCoreString* s) {
    return rt_core_unregister_immortal_ptr(s);
}

static int rt_core_register_float(RtCoreFloat* f) {
    return rt_core_register_scoped_immortal(f, &f->transient_scope_id);
}

static int rt_core_is_registered_float(RtCoreFloat* f) {
    return rt_core_is_registered_immortal_ptr(f);
}

/* Return the boxed RtCoreFloat if `value` is a registered heap-float, else NULL.
 * The registry membership test is done BEFORE reading ->kind, guarding the
 * tag-collision SEGV class. */
static inline RtCoreFloat* rt_core_as_heap_float(int64_t value) {
    if ((((uint64_t)value) & RT_VALUE_TAG_MASK) != RT_VALUE_TAG_HEAP) return NULL;
    RtCoreFloat* f = (RtCoreFloat*)(uintptr_t)(((uint64_t)value) & ~RT_VALUE_TAG_MASK);
    if (!f) return NULL;
    if (!rt_core_is_registered_float(f)) return NULL;
    if (f->kind != RT_VALUE_HEAP_FLOAT) return NULL;
    return f;
}

/* Return the boxed wide integer if `value` is a registered heap-int, else NULL.
 * Registry membership is checked BEFORE any dereference (same tag-collision
 * guard as rt_core_as_heap_float). */
static inline RtCoreWideInt* rt_core_as_heap_int(int64_t value) {
    if ((((uint64_t)value) & RT_VALUE_TAG_MASK) != RT_VALUE_TAG_HEAP) return NULL;
    RtCoreWideInt* n = (RtCoreWideInt*)(uintptr_t)(((uint64_t)value) & ~RT_VALUE_TAG_MASK);
    if (!n) return NULL;
    if (!rt_core_is_registered_immortal_ptr(n)) return NULL;
    if (n->kind != RT_VALUE_HEAP_INT) return NULL;
    return n;
}

/* Return the boxed unsigned wide integer if `value` is a registered heap-uint,
 * else NULL. Registry membership is checked BEFORE any dereference (same
 * tag-collision guard as rt_core_as_heap_float / rt_core_as_heap_int), so a
 * stray i64 that merely aliases TAG_HEAP is never dereferenced. */
static inline RtCoreUInt* rt_core_as_heap_uint(int64_t value) {
    if ((((uint64_t)value) & RT_VALUE_TAG_MASK) != RT_VALUE_TAG_HEAP) return NULL;
    RtCoreUInt* u = (RtCoreUInt*)(uintptr_t)(((uint64_t)value) & ~RT_VALUE_TAG_MASK);
    if (!u) return NULL;
    if (!rt_core_is_registered_immortal_ptr(u)) return NULL;
    if (u->kind != RT_VALUE_HEAP_UINT) return NULL;
    return u;
}

/* True when `v` survives the 61-bit tagged-immediate payload intact, i.e.
 * (v << 3) >> 3 == v. */
static inline int rt_core_int_fits_tagged(int64_t v) {
    return v >= -(int64_t)1152921504606846976LL && v < (int64_t)1152921504606846976LL;
}

static inline int64_t rt_core_from_special(uint64_t payload) {
    return (int64_t)((payload << 3) | RT_VALUE_TAG_SPECIAL);
}

static inline int64_t rt_core_nil(void) {
    return rt_core_from_special(RT_VALUE_SPECIAL_NIL);
}

static inline int rt_core_is_int(int64_t value) {
    return (((uint64_t)value) & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_INT;
}

static inline int rt_core_is_heap(int64_t value) {
    return (((uint64_t)value) & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_HEAP;
}

static inline int rt_core_is_float(int64_t value) {
    /* Heap-boxed (new, lossless) or legacy inline TAG_FLOAT. */
    if ((((uint64_t)value) & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_FLOAT) return 1;
    return rt_core_as_heap_float(value) != NULL;
}

static inline int rt_core_is_special(int64_t value) {
    return (((uint64_t)value) & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_SPECIAL;
}

static inline int64_t rt_core_as_int(int64_t value) {
    return value >> 3;
}

static inline double rt_core_as_float(int64_t value) {
    /* Heap-boxed float: return the full stored double (lossless). */
    RtCoreFloat* f = rt_core_as_heap_float(value);
    if (f) return f->value;
    /* Legacy inline TAG_FLOAT (low 3 mantissa bits already lost at box time). */
    uint64_t bits = ((uint64_t)value) & ~RT_VALUE_TAG_MASK;
    double result;
    memcpy(&result, &bits, sizeof(result));
    return result;
}

static inline uint64_t rt_core_special_payload(int64_t value) {
    return ((uint64_t)value) >> 3;
}

static inline int64_t rt_core_numeric_arg(int64_t value) {
    uint64_t raw = (uint64_t)value;
    if ((raw & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_INT && raw >= 8) {
        /* ARITHMETIC shift: boxed negatives are (v << 3); a logical >>3 turned
         * boxed -1 into 2305843009213693951 instead of -1. */
        return value >> 3;
    }
    {   /* Wide integers are heap-boxed, not tagged immediates. */
        RtCoreWideInt* n = rt_core_as_heap_int(value);
        if (n) return n->value;
    }
    return value;
}

static inline RtCoreString* rt_core_as_string(int64_t value) {
    uintptr_t raw = (uintptr_t)value;
    if (raw < 4096) return NULL;
    if ((raw & RT_VALUE_TAG_MASK) != RT_VALUE_TAG_HEAP) return NULL;
    RtCoreString* s = (RtCoreString*)(raw & ~RT_VALUE_TAG_MASK);
    if (!rt_core_is_registered_string(s)) return NULL;
    if (!s || s->kind != RT_VALUE_HEAP_STRING) return NULL;
    return s;
}

static atomic_bool rt_core_invalid_array_reported = ATOMIC_VAR_INIT(false);

static void rt_core_report_invalid_array_once(int64_t value) {
    if (atomic_exchange_explicit(
            &rt_core_invalid_array_reported, true, memory_order_relaxed)) {
        return;
    }
    fprintf(stderr,
            "[simple-runtime][error] rejected invalid array handle before "
            "dereference; probable compiler/FFI ABI mismatch "
            "(value_bits=0x%016llx)\n",
            (unsigned long long)(uint64_t)value);
}

static inline RtCoreArray* rt_core_as_array(int64_t value) {
    uintptr_t raw = (uintptr_t)value;
    if (raw < 4096) {
        if ((raw & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_HEAP) {
            rt_core_report_invalid_array_once(value);
        }
        return NULL;
    }
    if ((raw & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_HEAP) {
        raw &= ~RT_VALUE_TAG_MASK;
    } else if ((raw & RT_VALUE_TAG_MASK) != 0) {
        return NULL;
    }
    RtCoreArray* a = (RtCoreArray*)raw;
    /* Low tag bits alone do not prove this is a heap object.  Flat scalar
     * payloads such as 9, 17, and -7 have the same bit shape.  Prove registry
     * ownership before reading the header so a compiler/ABI defect is logged
     * and rejected instead of becoming a wild-pointer SIGSEGV. */
    if (!rt_core_is_registered_immortal_ptr(a)) {
        rt_core_report_invalid_array_once(value);
        return NULL;
    }
    if (a->kind != RT_VALUE_HEAP_ARRAY) return NULL;
    if (a->len < 0 || a->cap < 0 || a->len > a->cap || a->cap > RT_CORE_ARRAY_MAX_CAP) return NULL;
    return a;
}

static inline RtCoreArray* rt_core_as_registered_array(int64_t value) {
    uintptr_t raw = (uintptr_t)value;
    if (raw < 4096) return NULL;
    if ((raw & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_HEAP) {
        raw &= ~RT_VALUE_TAG_MASK;
    } else if ((raw & RT_VALUE_TAG_MASK) != 0) {
        return NULL;
    }
    RtCoreArray* array = (RtCoreArray*)raw;
    return rt_core_is_registered_array(array) ? rt_core_as_array(value) : NULL;
}

static inline RtCoreMutex* rt_core_as_mutex(int64_t value) {
    if (!rt_core_is_heap(value)) return NULL;
    RtCoreMutex* mutex = (RtCoreMutex*)(uintptr_t)(((uint64_t)value) & ~RT_VALUE_TAG_MASK);
    if (!rt_core_is_registered_mutex(mutex)) return NULL;
    return mutex->kind == RT_VALUE_HEAP_MUTEX ? mutex : NULL;
}

static inline RtCoreEnum* rt_core_as_enum(int64_t value) {
    if (!rt_core_is_heap(value)) return NULL;
    RtCoreEnum* e = (RtCoreEnum*)(uintptr_t)(((uint64_t)value) & ~RT_VALUE_TAG_MASK);
    if (!e) return NULL;
    /* Registry membership is a pure pointer comparison -- it must be checked
     * BEFORE dereferencing e->kind. A flat i64?/bool? payload that merely
     * aliases the HEAP tag bits (e.g. 9, 17, -7 -- see comment above the
     * registry definition) is never registered, so it safely resolves to
     * NULL here instead of being read as a wild pointer. */
    if (!rt_core_is_registered_enum(e)) return NULL;
    if (e->kind != RT_VALUE_HEAP_ENUM) return NULL;
    return e;
}

static inline RtCoreEnum* rt_core_as_registered_enum(int64_t value) {
    if (!rt_core_is_heap(value)) return NULL;
    RtCoreEnum* result =
        (RtCoreEnum*)(uintptr_t)(((uint64_t)value) & ~RT_VALUE_TAG_MASK);
    return rt_core_is_registered_enum(result) ? rt_core_as_enum(value) : NULL;
}

static inline RtCoreArray* rt_core_array_ptr(SplArray* value) {
    return rt_core_as_array((int64_t)(uintptr_t)value);
}

enum {
    RT_CORE_TRANSIENT_STRING,
    RT_CORE_TRANSIENT_ARRAY,
    RT_CORE_TRANSIENT_DICT,
    RT_CORE_TRANSIENT_ENUM,
    RT_CORE_TRANSIENT_FLOAT,
    RT_CORE_TRANSIENT_CLOSURE,
    RT_CORE_TRANSIENT_RAW
};

typedef struct RtCoreTransientNode {
    void* ptr;
    uint8_t kind;
    size_t bytes;
} RtCoreTransientNode;

typedef struct RtCoreTransientPlan {
    RtCoreTransientNode* nodes;
    size_t len;
    size_t cap;
    uintptr_t* seen;
    size_t seen_cap;
    size_t seen_len;
} RtCoreTransientPlan;

#define RT_CORE_TRANSIENT_MAX_NODES ((size_t)1 << 22)

static int rt_core_transient_seen_insert(RtCoreTransientPlan* plan, uintptr_t ptr) {
    if ((plan->seen_len + 1) * 10 >= plan->seen_cap * 7) {
        size_t next_cap = plan->seen_cap == 0 ? 256 : plan->seen_cap * 2;
        if (next_cap > SIZE_MAX / sizeof(uintptr_t)) return -1;
        uintptr_t* fresh = (uintptr_t*)calloc(next_cap, sizeof(uintptr_t));
        if (!fresh) return -1;
        size_t mask = next_cap - 1;
        for (size_t i = 0; i < plan->seen_cap; i++) {
            uintptr_t entry = plan->seen[i];
            if (!entry) continue;
            size_t j = rt_core_immortal_hash_ptr(entry) & mask;
            while (fresh[j]) j = (j + 1) & mask;
            fresh[j] = entry;
        }
        free(plan->seen);
        plan->seen = fresh;
        plan->seen_cap = next_cap;
    }
    size_t mask = plan->seen_cap - 1;
    size_t i = rt_core_immortal_hash_ptr(ptr) & mask;
    for (;;) {
        if (!plan->seen[i]) {
            plan->seen[i] = ptr;
            plan->seen_len++;
            return 1;
        }
        if (plan->seen[i] == ptr) return 0;
        i = (i + 1) & mask;
    }
}

static int rt_core_transient_plan_push(
    RtCoreTransientPlan* plan, void* ptr, uint8_t kind, size_t bytes) {
    if (plan->len == plan->cap) {
        size_t next_cap = plan->cap == 0 ? 32 : plan->cap * 2;
        if (next_cap > RT_CORE_TRANSIENT_MAX_NODES) return 0;
        RtCoreTransientNode* fresh = (RtCoreTransientNode*)realloc(
            plan->nodes, next_cap * sizeof(RtCoreTransientNode));
        if (!fresh) return 0;
        plan->nodes = fresh;
        plan->cap = next_cap;
    }
    plan->nodes[plan->len++] = (RtCoreTransientNode){ptr, kind, bytes};
    return 1;
}

/* 1 = tracked node, 0 = immediate or persistent string, -1 = invalid node. */
static int rt_core_transient_classify(int64_t value, RtCoreTransientNode* node) {
    uintptr_t raw = (uintptr_t)value;
    uintptr_t raw_ptr = raw & RT_VALUE_TAG_MASK ? raw & ~RT_VALUE_TAG_MASK : raw;
    RtCoreTransientRawAlloc* allocation = rt_core_transient_raw_lookup(raw_ptr);
    if (allocation) {
        *node = (RtCoreTransientNode){
            (void*)raw_ptr, RT_CORE_TRANSIENT_RAW,
            allocation->bytes & RT_CORE_TRANSIENT_RAW_SIZE_MASK};
        return 1;
    }
    if (!rt_core_is_heap(value)) return 0;
    void* ptr = (void*)(uintptr_t)(((uint64_t)value) & ~RT_VALUE_TAG_MASK);
    if (rt_core_is_registered_immortal_ptr(ptr)) {
        switch (rt_core_registered_object_kind(ptr)) { /* membership checked first */
            case RT_VALUE_HEAP_ARRAY:
                *node = (RtCoreTransientNode){ptr, RT_CORE_TRANSIENT_ARRAY, 0};
                return 1;
            case RT_VALUE_HEAP_DICT:
                *node = (RtCoreTransientNode){ptr, RT_CORE_TRANSIENT_DICT, 0};
                return 1;
            case RT_VALUE_HEAP_ENUM:
                *node = (RtCoreTransientNode){ptr, RT_CORE_TRANSIENT_ENUM, 0};
                return 1;
            case RT_VALUE_HEAP_FLOAT:
            case RT_VALUE_HEAP_INT:   /* identical leaf layout */
            case RT_VALUE_HEAP_UINT:  /* identical leaf layout */
                *node = (RtCoreTransientNode){ptr, RT_CORE_TRANSIENT_FLOAT, 0};
                return 1;
            case RT_VALUE_HEAP_CLOSURE:
                *node = (RtCoreTransientNode){ptr, RT_CORE_TRANSIENT_CLOSURE, 0};
                return 1;
            case RT_VALUE_HEAP_STRING:
                if ((((RtCoreString*)ptr)->reserved & RT_CORE_STRING_FLAG_TRANSIENT) != 0 &&
                    (((RtCoreString*)ptr)->reserved & RT_CORE_STRING_FLAG_SHARED) == 0) {
                    *node = (RtCoreTransientNode){ptr, RT_CORE_TRANSIENT_STRING, 0};
                    return 1;
                }
                return 0;
            default:
                return -1;
        }
    }
    return 0;
}

static int rt_core_transient_add(RtCoreTransientPlan* plan, int64_t value) {
    RtCoreTransientNode node;
    int classified = rt_core_transient_classify(value, &node);
    if (classified < 0) return -1;
    if (classified == 0) return 1;
    int seen = rt_core_transient_seen_insert(plan, (uintptr_t)node.ptr);
    if (seen < 0) return -1;
    if (!seen) return 1;
    return rt_core_transient_plan_push(plan, node.ptr, node.kind, node.bytes) ? 1 : -1;
}

int8_t rt_transient_heap_promote(int64_t value) {
    if (!rt_core_transient_array_scope_active || !rt_core_transient_array_scope_paused) return 0;
    rt_core_heap_lifecycle_acquire();
    RtCoreTransientPlan plan = {0};
    RtCoreTransientNode root;
    int ok = rt_core_transient_classify(value, &root) == 1 &&
        rt_core_transient_add(&plan, value) == 1;
    for (size_t i = 0; ok && i < plan.len; i++) {
        RtCoreTransientNode node = plan.nodes[i];
        if (node.kind == RT_CORE_TRANSIENT_ARRAY) {
            RtCoreArray* array = (RtCoreArray*)node.ptr;
            if (array->flags & (RT_CORE_ARRAY_FLAG_BYTES | RT_CORE_ARRAY_FLAG_U64_PACKED)) continue;
            for (int64_t j = 0; j < array->len && ok; j++) {
                ok = rt_core_transient_add(&plan, ((int64_t*)array->data)[j]) == 1;
            }
        } else if (node.kind == RT_CORE_TRANSIENT_DICT) {
            RtCoreDict* dict = (RtCoreDict*)node.ptr;
            for (int64_t j = 0; j < dict->cap && ok; j++) {
                RtCoreDictEntry* entry = &dict->entries[j];
                if (entry->occupied != 1) continue;
                ok = rt_core_transient_add(&plan, entry->key) == 1 &&
                    rt_core_transient_add(&plan, entry->value) == 1;
            }
        } else if (node.kind == RT_CORE_TRANSIENT_ENUM) {
            ok = rt_core_transient_add(&plan, ((RtCoreEnum*)node.ptr)->payload) == 1;
        } else if (node.kind == RT_CORE_TRANSIENT_CLOSURE) {
            RtCoreClosure* closure = (RtCoreClosure*)node.ptr;
            for (int64_t j = 0; j < closure->capture_count && ok; j++) {
                ok = rt_core_transient_add(&plan, closure->captures[j]) == 1;
            }
        } else if (node.kind == RT_CORE_TRANSIENT_RAW) {
            for (size_t offset = 0; offset + sizeof(int64_t) <= node.bytes && ok;
                    offset += sizeof(int64_t)) {
                int64_t child;
                memcpy(&child, (const uint8_t*)node.ptr + offset, sizeof(child));
                ok = rt_core_transient_add(&plan, child) == 1;
            }
        }
    }
    if (ok) {
        const uint32_t scope_id = rt_core_transient_array_scope_id;
        for (size_t i = 0; i < plan.len; i++) {
            RtCoreTransientNode node = plan.nodes[i];
            uint32_t* object_scope = NULL;
            switch (node.kind) {
                case RT_CORE_TRANSIENT_STRING:
                    ((RtCoreString*)node.ptr)->reserved &= ~RT_CORE_STRING_FLAG_TRANSIENT;
                    break;
                case RT_CORE_TRANSIENT_ARRAY: object_scope = &((RtCoreArray*)node.ptr)->transient_scope_id; break;
                case RT_CORE_TRANSIENT_DICT: object_scope = &((RtCoreDict*)node.ptr)->transient_scope_id; break;
                case RT_CORE_TRANSIENT_ENUM: object_scope = &((RtCoreEnum*)node.ptr)->transient_scope_id; break;
                case RT_CORE_TRANSIENT_FLOAT: object_scope = &((RtCoreFloat*)node.ptr)->transient_scope_id; break;
                case RT_CORE_TRANSIENT_CLOSURE: object_scope = &((RtCoreClosure*)node.ptr)->transient_scope_id; break;
                case RT_CORE_TRANSIENT_RAW: {
                    RtCoreTransientRawAlloc* raw =
                        rt_core_transient_raw_lookup((uintptr_t)node.ptr);
                    if (raw) raw->bytes &= RT_CORE_TRANSIENT_RAW_SIZE_MASK;
                    break;
                }
            }
            if (object_scope && *object_scope == scope_id) *object_scope = 0;
        }
    }
    free(plan.nodes);
    free(plan.seen);
    rt_core_heap_lifecycle_release();
    return ok ? 1 : 0;
}

static int8_t rt_core_array_reserve(SplArray* a, int64_t min_cap);

static void rt_core_write_bytes(FILE* stream, const uint8_t* ptr, uint64_t len) {
    if (!ptr || len == 0) return;
    fwrite(ptr, 1, (size_t)len, stream);
}

/* Defined further below in this file (after the aggregate formatters it
 * dispatches to); forward-declared here so the direct-print path below can
 * delegate tuple/array/dict/Option/Result formatting to the SAME dispatch
 * rt_to_string uses, instead of duplicating it. */
int64_t rt_to_string(int64_t value);

static void rt_core_print_value_to(FILE* stream, int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (s) {
        rt_core_write_bytes(stream, (const uint8_t*)s->data, s->len);
        return;
    }

    if (rt_core_is_int(value)) {
        fprintf(stream, "%lld", (long long)rt_core_as_int(value));
        return;
    }

    {   /* Heap-boxed wide integer (>= 2^60): print the real value, not a ptr. */
        RtCoreWideInt* wide = rt_core_as_heap_int(value);
        if (wide) {
            fprintf(stream, "%lld", (long long)wide->value);
            return;
        }
    }

    if (rt_core_is_special(value)) {
        switch (rt_core_special_payload(value)) {
            case RT_VALUE_SPECIAL_NIL:
                return;
            case RT_VALUE_SPECIAL_TRUE:
                fputs("true", stream);
                return;
            case RT_VALUE_SPECIAL_FALSE:
                fputs("false", stream);
                return;
            default:
                fprintf(stream, "<special:%llu>", (unsigned long long)rt_core_special_payload(value));
                return;
        }
    }

    /* Aggregates (tuple/array/dict/Option/Result) and any other value rt_to_string
     * recognizes: delegate so this direct-print path matches rt_to_string's
     * output exactly. rt_to_string itself falls back to the same
     * "<value:0x..>" marker for anything neither path recognizes, so this
     * subsumes the old inline fprintf without changing that fallback's text. */
    int64_t formatted = rt_to_string(value);
    RtCoreString* fs = rt_core_as_string(formatted);
    if (fs) {
        rt_core_write_bytes(stream, (const uint8_t*)fs->data, fs->len);
        return;
    }

    fprintf(stream, "<value:0x%llx>", (unsigned long long)(uint64_t)value);
}

/* ================================================================
 * I/O Operations
 * ================================================================ */

void rt_print(const char* s) {
    spl_print(s);
}

void rt_println(const char* s) {
    spl_println(s);
}

char* rt_readline(void) {
    char buf[4096];
    if (fgets(buf, sizeof(buf), stdin)) {
        /* Strip trailing newline */
        size_t len = strlen(buf);
        if (len > 0 && buf[len - 1] == '\n') buf[len - 1] = '\0';
        return spl_str_new(buf);
    }
    return spl_str_new("");
}

char* rt_stdin_read_line(void) {
    char buf[4096];
    if (fgets(buf, sizeof(buf), stdin)) {
        size_t len = strlen(buf);
        if (len > 0 && buf[len - 1] == '\n') buf[len - 1] = '\0';
        return spl_str_new(buf);
    }
    return NULL; /* EOF */
}

int64_t rt_stdin_read_line_text(void) {
    char buf[4096];
    if (!fgets(buf, sizeof(buf), stdin)) {
        return rt_string_new(NULL, 0);
    }
    return rt_string_new((const uint8_t*)buf, (int64_t)strlen(buf));
}

int64_t rt_stdin_read_chars_text(int64_t count) {
    if (count <= 0) {
        return rt_string_new(NULL, 0);
    }
    char* buf = (char*)malloc((size_t)count);
    if (!buf) {
        return rt_string_new(NULL, 0);
    }
    size_t n = fread(buf, 1, (size_t)count, stdin);
    int64_t value = rt_string_new((const uint8_t*)buf, (int64_t)n);
    free(buf);
    return value;
}

int64_t stdin_read_char(void) {
    int ch = fgetc(stdin);
    if (ch == EOF) {
        return rt_string_new(NULL, 0);
    }
    uint8_t byte = (uint8_t)ch;
    return rt_string_new(&byte, 1);
}

int64_t rt_stdout_write_text(const char* s) {
    if (!s) return 0;
    int64_t len = (int64_t)strlen(s);
    fputs(s, stdout);
    return len;
}

int64_t print_raw(int64_t value) {
    rt_core_print_value_to(stdout, value);
    fflush(stdout);
    return 0;
}

int64_t rt_stdout_write(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (s) {
        rt_core_write_bytes(stdout, (const uint8_t*)s->data, s->len);
        return (int64_t)s->len;
    }
    rt_core_print_value_to(stdout, value);
    return 0;
}

void rt_stdout_flush(void) {
    fflush(stdout);
}

int64_t rt_stderr_write(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (s) {
        rt_core_write_bytes(stderr, (const uint8_t*)s->data, s->len);
        return (int64_t)s->len;
    }
    rt_core_print_value_to(stderr, value);
    return 0;
}

void rt_stderr_flush(void) {
    fflush(stderr);
}

/* Forward declaration: rt_value_int_wide is defined just below, but is called
 * from rt_value_int above it. Without this, C99 implicit-declaration rules make
 * the call default to `int (*)()`, which clang rejects outright
 * (-Wimplicit-function-declaration, then "conflicting types") and which fails
 * the whole runtime_native.c compile -- blocking every native-build/AOT run. */
int64_t rt_value_int_wide(int64_t value);

int64_t rt_value_int(int64_t value) {
    if (!rt_core_int_fits_tagged(value)) return rt_value_int_wide(value);
    return (int64_t)(((uint64_t)value << 3) | RT_VALUE_TAG_INT);
}

/* Range-checked integer box (ABI contract §1.1). Values inside the 61-bit
 * payload keep the classic `v << 3` immediate -- bit-identical to before, so no
 * existing consumer changes behavior. Values that do NOT fit are heap-boxed
 * losslessly instead of being silently truncated. */
int64_t rt_value_int_wide(int64_t value) {
    if (rt_core_int_fits_tagged(value)) {
        return (int64_t)(((uint64_t)value << 3) | RT_VALUE_TAG_INT);
    }
    RtCoreWideInt* n = (RtCoreWideInt*)malloc(sizeof(RtCoreWideInt));
    if (!n) {
        /* OOM: the truncating form is still wrong, but crashing here is worse. */
        return (int64_t)(((uint64_t)value << 3) | RT_VALUE_TAG_INT);
    }
    n->kind = RT_VALUE_HEAP_INT;
    n->transient_scope_id = 0;
    n->value = value;
    if (!rt_core_register_scoped_immortal(n, &n->transient_scope_id)) {
        free(n);
        return (int64_t)(((uint64_t)value << 3) | RT_VALUE_TAG_INT);
    }
    return (int64_t)(((uint64_t)(uintptr_t)n) | RT_VALUE_TAG_HEAP);
}

/* Mirror unbox for rt_value_int_wide: heap-boxed wide int, else the plain
 * arithmetic `>> 3` the tagged immediate has always used. */
int64_t rt_value_as_int_wide(int64_t value) {
    RtCoreWideInt* n = rt_core_as_heap_int(value);
    if (n) return n->value;
    /* bug native_empty_dict_text_value_sigsegv_2026-07-20: codegen emits this
     * unbox on EVERY container read whose static element type is the erased i64
     * default -- including a `var d = {}` dict that actually holds text. A
     * tagged HEAP handle (string/float/array/class) is not an int box, and the
     * blind `>> 3` below shredded it into a non-pointer word; the very next
     * rt_text_eq_any -> rt_interp_cstr then treated that word as a raw char*
     * and strcmp SIGSEGV'd (observed strcmp rdi=0xaaaaaaac182, i.e. a real
     * handle 0x5555_5556_0C10 arithmetically shifted right by 3).
     *
     * A heap handle carries no integer to extract, so pass it through
     * unchanged and let the downstream string/float path decode it properly.
     * Values that ARE tagged int immediates (and the nil/special sentinels,
     * whose `>> 3` behaviour other lowering deliberately relies on -- see
     * dict_get_preserve_flat_nil) keep the exact previous arithmetic, so no
     * correct existing consumer changes behaviour. */
    if ((((uint64_t)value) & 0x7ULL) == RT_VALUE_TAG_HEAP) return value;
    return value >> 3;
}

/* Box a raw u64 bit pattern losslessly (ABI contract §1.1, unsigned arm).
 *
 * ALWAYS boxes -- the small-value fast path lives in the CALLER
 * (rt_core_value_u64_compact returns rt_value_int for anything that fits the
 * signed tagged immediate), exactly as the pure-Simple twin
 * src/runtime/simple_core/core_values.spl:29 does. Allocation, magic write,
 * zeroed scope id, immortal-registry registration and the OOM fallback all
 * mirror rt_value_int_wide above; the twin's `calloc(1, 16)` is reproduced by
 * malloc + explicit field initialisation of the same 16-byte layout.
 *
 * On registration failure the value is returned as the truncating tagged
 * immediate. That is lossy for a wide u64, but it is the same
 * degrade-don't-crash choice rt_value_int_wide and rt_value_float already make,
 * and it is only reachable on OOM. */
int64_t rt_value_u64(int64_t bits) {
    RtCoreUInt* u = (RtCoreUInt*)malloc(sizeof(RtCoreUInt));
    if (!u) return (int64_t)(((uint64_t)bits << 3) | RT_VALUE_TAG_INT);
    u->kind = RT_VALUE_HEAP_UINT;
    u->transient_scope_id = 0;
    u->value = (uint64_t)bits;
    if (!rt_core_register_scoped_immortal(u, &u->transient_scope_id)) {
        free(u);
        return (int64_t)(((uint64_t)bits << 3) | RT_VALUE_TAG_INT);
    }
    return (int64_t)(((uint64_t)(uintptr_t)u) | RT_VALUE_TAG_HEAP);
}

/* Mirror unbox for rt_value_u64: the raw u64 bit pattern, returned in an
 * int64_t carrier (the ABI has no unsigned return type -- callers reinterpret).
 *
 * The heap-uint arm and the trailing `value >> 3` are the twin's
 * (core_values.spl:37). The middle arm is additional: this C runtime also has a
 * SIGNED wide box, which the simple-core twin does not, and an element read
 * through rt_value_as_u64 (rt_array_get's non-U64_PACKED path) can legitimately
 * hold one. Without this arm such a box would be `>> 3`-mangled into a pointer
 * fragment. It cannot misfire: rt_core_as_heap_int is registry-guarded. */
int64_t rt_value_as_u64(int64_t value) {
    RtCoreUInt* u = rt_core_as_heap_uint(value);
    if (u) return (int64_t)u->value;
    RtCoreWideInt* n = rt_core_as_heap_int(value);
    if (n) return n->value;
    return value >> 3;
}

/* Total, tag-aware `UnboxInt` decode for compiled code -- the C twin of the Rust
 * seed's rt_value_unbox_int (runtime/src/value/sffi/value_ops.rs), emitted by the
 * Cranelift UnboxInt lowering:
 *
 *   heap-boxed WIDE int -> its full i64 value;
 *   TAG_INT scalar      -> value >> 3;
 *   tagged true/false   -> 1 / 0;
 *   anything else       -> passed through VERBATIM, so a heap enum/string handle
 *                          is not >>3-mangled (Task #123).
 *
 * Safe on ANY input, including a raw untagged i64 -- that totality is what lets
 * codegen replace an inline select chain with a single call. */
int64_t rt_value_unbox_int(int64_t value) {
    RtCoreWideInt* n = rt_core_as_heap_int(value);
    if (n) return n->value;
    if ((((uint64_t)value) & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_INT) return value >> 3;
    if (value == 11) return 1;  /* TAG_SPECIAL | SPECIAL_TRUE  */
    if (value == 19) return 0;  /* TAG_SPECIAL | SPECIAL_FALSE */
    return value;
}

static int64_t rt_core_value_u64_compact(int64_t bits) {
    uint64_t value = (uint64_t)bits;
    if (value <= (uint64_t)(INT64_MAX >> 3)) return rt_value_int((int64_t)value);
    return rt_value_u64(bits);
}

int64_t rt_value_as_int(int64_t value) {
    /* TEXT reaching an integer cast must be DECODED, not bit-shifted.
     *
     * This function backs the `ANY -> int` cast arm on the compiled lanes, and
     * `char_at` has no static return type, so `s.char_at(i) as i64` falls
     * through to ANY and lands here. A bare `value >> 3` is correct for a
     * tagged int (TAG_INT == 0x0, so a boxed int is v << 3) but pure garbage
     * for a TAG_HEAP value: it yields the string's raw allocation address >> 3,
     * a different number on every run. Nothing can depend on the old answer.
     *
     * Same defect and same resolution as the Rust seed twin (22c983762d0);
     * this is the copy the SELF-HOSTED binary links.
     *
     * The guard is deliberately rt_core_as_string(), which is REGISTRY-
     * VALIDATED (rejects raw < 4096, requires TAG_HEAP, requires membership in
     * the string registry and kind == RT_VALUE_HEAP_STRING) -- NOT a bare
     * `(value & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_HEAP` test. That distinction
     * is load-bearing: TAG_HEAP is 0x1, so every ODD value would test as "heap",
     * and two pure-Simple call sites pass a RAW, UNTAGGED i64 here and depend on
     * the bare shift -- `rt_value_as_int(load_symbol_slot >> 32)` and
     * `rt_value_as_int(packed_return_local & 0xFFFFFFFF)`, both in
     * src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl (:700, :1011).
     * Pinned by P4 of src/runtime/test/rt_value_as_int_text_decode_selfcheck.c.
     *
     * Text of exactly one codepoint yields THAT CODE POINT, matching the
     * tree-walk interpreter's contract ("only int, float, bool, and single-char
     * strings can be cast to numeric types"). Longer text falls back to
     * rt_string_to_int_lenient, the same parse the STRING-typed cast arm
     * already uses, so `int(text)` is unchanged in shape. */
    RtCoreString* s = rt_core_as_string(value);
    if (s) {
        if (s->len > 0) {
            /* Width of the FIRST codepoint, from its lead byte. If that width
             * spans the whole string, the text is exactly one codepoint. */
            uint8_t b0 = (uint8_t)s->data[0];
            uint64_t width = 1;
            if (b0 >= 194 && b0 <= 223) width = 2;
            else if (b0 >= 224 && b0 <= 239) width = 3;
            else if (b0 >= 240 && b0 <= 244) width = 4;
            if (width == s->len) return rt_string_char_code_at(value, 0);
        }
        return rt_string_to_int_lenient(value);
    }
    return rt_value_as_int_wide(value);
}

/* Box an f64 into the tagged RuntimeValue representation. Floats are
 * HEAP-BOXED (lossless): the old inline TAG_FLOAT form kept only (bits & ~7),
 * zeroing the low 3 mantissa bits, so a container/Any float lost precision. We
 * allocate an RtCoreFloat leaf holding the full double and return a TAG_HEAP
 * pointer. Scalar/arithmetic f64 held in native registers never reaches here --
 * only values that enter the tagged representation box.
 *
 * ABI: the parameter is a `double`, NOT the raw i64 bit pattern. Every compiler
 * backend emits the call that way -- `RuntimeFuncSpec::new("rt_value_float",
 * &[F64], &[I64])` in codegen/runtime_sffi.rs, and the LLVM backend builds
 * `call @rt_value_float(double ...)` -- and the Rust runtime's
 * `pub extern "C" fn rt_value_float(f: f64)` already agrees. This C runtime was
 * the sole outlier: declaring the parameter as `int64_t` made it read %rdi
 * under SysV x86-64 while the caller passed the value in %xmm0, so EVERY f64
 * boxed in the native lane picked up an unrelated integer register and printed
 * as denormal garbage. Keep this a `double`; the bit pattern is recovered by
 * memcpy below. See doc/08_tracking/bug/
 * native_lane_prints_every_f64_as_denormal_garbage_2026-08-10.md. */
int64_t rt_value_float(double value_f64) {
    int64_t raw_bits = 0;
    memcpy(&raw_bits, &value_f64, sizeof(raw_bits));
    RtCoreFloat* f = (RtCoreFloat*)malloc(sizeof(RtCoreFloat));
    if (!f) {
        /* OOM: fall back to the legacy lossy inline form rather than crash. */
        return (int64_t)(((uint64_t)raw_bits & ~RT_VALUE_TAG_MASK) | RT_VALUE_TAG_FLOAT);
    }
    f->kind = RT_VALUE_HEAP_FLOAT;
    memcpy(&f->value, &raw_bits, sizeof(f->value));
    if (!rt_core_register_float(f)) {
        free(f);
        return (int64_t)(((uint64_t)raw_bits & ~RT_VALUE_TAG_MASK) | RT_VALUE_TAG_FLOAT);
    }
    return (int64_t)(((uint64_t)(uintptr_t)f) | RT_VALUE_TAG_HEAP);
}

/* Unbox a tagged RuntimeValue to its f64. Dual-aware: reads the heap-boxed form
 * (lossless) and the legacy inline TAG_FLOAT form. This is the runtime target of
 * the codegen float-unbox at the container boundary (decode_runtime_value). */
double rt_value_as_float(int64_t value) {
    return rt_core_as_float(value);
}

/* Detect a float (heap-boxed or legacy inline TAG_FLOAT). */
int8_t rt_value_is_float(int64_t value) {
    return rt_core_is_float(value) ? 1 : 0;
}

int64_t rt_value_bool(int64_t value) {
    return rt_core_from_special(value ? RT_VALUE_SPECIAL_TRUE : RT_VALUE_SPECIAL_FALSE);
}

int64_t rt_value_nil(void) {
    return rt_core_nil();
}

int64_t rt_function_not_found(const uint8_t* name, uint64_t len) {
    fputs("Simple runtime error: function not found", stderr);
    if (name && len > 0) {
        fputs(": ", stderr);
        fwrite(name, 1, (size_t)len, stderr);
    }
    fputc('\n', stderr);
    return rt_core_nil();
}

int64_t rt_interp_call(const uint8_t* name, uint64_t len, int64_t argc, int64_t argv) {
    (void)argc;
    (void)argv;
    return rt_function_not_found(name, len);
}

static int64_t rt_string_new_uncached_impl(
    const uint8_t* bytes, uint64_t len, int persistent) {
    if (!bytes && len > 0) return rt_core_nil();
    if (len > SIZE_MAX - sizeof(RtCoreString) - 1) return rt_core_nil();

    RtCoreString* s = (RtCoreString*)malloc(sizeof(RtCoreString) + (size_t)len + 1);
    if (!s) return rt_core_nil();
    s->kind = RT_VALUE_HEAP_STRING;
    s->reserved = 0;
    s->len = len;
    if (len > 0 && bytes) {
        memcpy(s->data, bytes, (size_t)len);
    }
    s->data[len] = '\0';
    if (!(persistent ? rt_core_register_persistent_string(s) : rt_core_register_string(s))) {
        free(s);
        return rt_core_nil();
    }
    return (int64_t)(((uint64_t)(uintptr_t)s) | RT_VALUE_TAG_HEAP);
}

static int64_t rt_string_new_uncached(const uint8_t* bytes, uint64_t len) {
    return rt_string_new_uncached_impl(bytes, len, 0);
}

static int64_t rt_string_new_uncached_persistent(const uint8_t* bytes, uint64_t len) {
    return rt_string_new_uncached_impl(bytes, len, 1);
}

int64_t rt_string_new(const uint8_t* bytes, uint64_t len) {
    if (!bytes && len > 0) return rt_core_nil();
    if (len > 1) return rt_string_new_uncached(bytes, len);

    size_t index = len == 0 ? 0 : (size_t)bytes[0] + 1;
    while (atomic_flag_test_and_set_explicit(&rt_core_short_string_cache_lock, memory_order_acquire)) { }
    RtCoreString* cached = rt_core_short_string_cache[index];
    if (!cached) {
        int64_t value = rt_string_new_uncached_persistent(bytes, len);
        cached = rt_core_as_string(value);
        if (cached) {
            /* process-wide shared: never freeable */
            cached->reserved |= RT_CORE_STRING_FLAG_SHARED;
            rt_core_short_string_cache[index] = cached;
        }
    }
    atomic_flag_clear_explicit(&rt_core_short_string_cache_lock, memory_order_release);
    return cached
        ? (int64_t)(((uint64_t)(uintptr_t)cached) | RT_VALUE_TAG_HEAP)
        : rt_core_nil();
}

int64_t rt_cstring_to_text(const char* cstr) {
    if (!cstr) return rt_string_new(NULL, 0);
    return rt_string_new((const uint8_t*)cstr, (uint64_t)strlen(cstr));
}

/* Interned boxing for compile-time string LITERALS only.
 *
 * Codegen emits one boxing call per literal *evaluation* and this runtime
 * never frees strings, so a hot literal comparison (`tok == "fn"`) leaked one
 * registered heap string per execution (~9 live objects per source char
 * during self-hosted parse -- see
 * doc/08_tracking/bug/bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md).
 * Literal bytes live in rodata: (address, len) is immutable and stable for
 * the process lifetime, so every evaluation of the same literal site can
 * share one boxed string. Callers MUST only pass static literal data. */
#define RT_LITERAL_INTERN_BUCKETS 65536u

typedef struct RtLiteralInternNode {
    const uint8_t* bytes;
    uint64_t len;
    int64_t value;
    struct RtLiteralInternNode* next;
} RtLiteralInternNode;

static RtLiteralInternNode* rt_literal_intern_table[RT_LITERAL_INTERN_BUCKETS];
static atomic_flag rt_literal_intern_lock = ATOMIC_FLAG_INIT;

int64_t rt_string_new_literal(const uint8_t* bytes, uint64_t len) {
    if (len <= 1) {
        /* rt_string_new already returns process-wide cached values here. */
        return rt_string_new(bytes, len);
    }
    uint64_t h = ((uint64_t)(uintptr_t)bytes) * 0x9E3779B97F4A7C15ull ^ len;
    uint32_t bucket = (uint32_t)(h >> 32) & (RT_LITERAL_INTERN_BUCKETS - 1u);

    while (atomic_flag_test_and_set_explicit(&rt_literal_intern_lock, memory_order_acquire)) { }
    for (RtLiteralInternNode* node = rt_literal_intern_table[bucket]; node; node = node->next) {
        if (node->bytes == bytes && node->len == len) {
            int64_t cached = node->value;
            atomic_flag_clear_explicit(&rt_literal_intern_lock, memory_order_release);
            return cached;
        }
    }
    atomic_flag_clear_explicit(&rt_literal_intern_lock, memory_order_release);

    int64_t value = rt_string_new_uncached_persistent(bytes, len);
    /* Interned literals are handed to every evaluation of that literal site,
     * so this object outlives any single holder: never freeable. */
    RtCoreString* interned = rt_core_as_string(value);
    if (interned) interned->reserved |= RT_CORE_STRING_FLAG_SHARED;
    RtLiteralInternNode* node = (RtLiteralInternNode*)malloc(sizeof(RtLiteralInternNode));
    if (!node) return value;
    node->bytes = bytes;
    node->len = len;
    node->value = value;

    while (atomic_flag_test_and_set_explicit(&rt_literal_intern_lock, memory_order_acquire)) { }
    node->next = rt_literal_intern_table[bucket];
    rt_literal_intern_table[bucket] = node;
    atomic_flag_clear_explicit(&rt_literal_intern_lock, memory_order_release);
    return value;
}

int64_t rt_string_len(int64_t string) {
    RtCoreString* s = rt_core_as_string(string);
    if (s) return (int64_t)s->len;
    return string >= 0x10000 ? (int64_t)strlen((const char*)(uintptr_t)string) : -1;
}

const uint8_t* rt_string_data(int64_t string) {
    RtCoreString* s = rt_core_as_string(string);
    return s ? (const uint8_t*)s->data : NULL;
}

int64_t rt_string_bytes(int64_t string) {
    RtCoreString* s = rt_core_as_string(string);
    SplArray* bytes = rt_array_new(s ? (int64_t)s->len : 0);
    if (!bytes) return rt_core_nil();
    if (s) {
        for (uint64_t i = 0; i < s->len; i++) {
            /* BUGFIX (byte_span_cross_module_misread_2026-07-19): store the RAW
             * byte, NOT rt_value_int(byte). `.bytes()` is declared `[u8]`; a
             * `[u8]` array (literal `[73u8,..]` / `push(u8)`) stores raw untagged
             * bytes and the `[u8]` element read truncates with `& 0xFF` without
             * untagging. rt_value_int tagged the slot as `byte << 3`, so `[u8]`
             * reads at param/struct-field/typed-var sites returned the tag's low
             * byte (73<<3=0x248 -> 0x48=72) instead of 73. Mirrors the pure-Simple
             * fix in simple_core/core_string.spl rt_string_bytes. */
            rt_array_push(bytes, (uint8_t)s->data[i]);
        }
    }
    return (int64_t)(uintptr_t)bytes;
}

int64_t rt_string_chars(int64_t string) {
    RtCoreString* s = rt_core_as_string(string);
    SplArray* chars = rt_array_new(s ? (int64_t)s->len : 0);
    if (!chars) return rt_core_nil();
    if (!s) return (int64_t)(uintptr_t)chars;

    for (uint64_t i = 0; i < s->len;) {
        uint8_t lead = (uint8_t)s->data[i];
        uint64_t width = 1;
        if (lead >= 0xc2 && lead <= 0xdf && i + 2 <= s->len) width = 2;
        else if (lead >= 0xe0 && lead <= 0xef && i + 3 <= s->len) width = 3;
        else if (lead >= 0xf0 && lead <= 0xf4 && i + 4 <= s->len) width = 4;
        rt_array_push(chars, rt_string_new((const uint8_t*)s->data + i, width));
        i += width;
    }
    return (int64_t)(uintptr_t)chars;
}

#define RT_STRING_BUILDER_MAGIC 0x534255445F313233ULL

typedef struct RtStringBuilder {
    uint64_t magic;
    size_t len;
    size_t cap;
    uint8_t* data;
} RtStringBuilder;

static RtStringBuilder* rt_string_builder_from_handle(int64_t handle) {
    if (handle == 0) return NULL;
    RtStringBuilder* builder = (RtStringBuilder*)(uintptr_t)handle;
    return builder->magic == RT_STRING_BUILDER_MAGIC ? builder : NULL;
}

int64_t rt_string_builder_new(void) {
    RtStringBuilder* builder = (RtStringBuilder*)calloc(1, sizeof(RtStringBuilder));
    if (!builder) return 0;
    builder->magic = RT_STRING_BUILDER_MAGIC;
    return (int64_t)(uintptr_t)builder;
}

int64_t rt_string_builder_push(int64_t handle, int64_t string) {
    RtStringBuilder* builder = rt_string_builder_from_handle(handle);
    RtCoreString* value = rt_core_as_string(string);
    if (!builder || !value) return 0;
    if (value->len == 0) return 1;
    if (value->len > SIZE_MAX - builder->len) return 0;

    size_t required = builder->len + (size_t)value->len;
    if (required > builder->cap) {
        size_t next_cap = builder->cap == 0 ? 64 : builder->cap;
        while (next_cap < required) {
            if (next_cap > SIZE_MAX / 2) {
                next_cap = required;
                break;
            }
            next_cap *= 2;
        }
        uint8_t* next = (uint8_t*)realloc(builder->data, next_cap);
        if (!next) return 0;
        builder->data = next;
        builder->cap = next_cap;
    }
    memcpy(builder->data + builder->len, value->data, (size_t)value->len);
    builder->len = required;
    return 1;
}

int64_t rt_string_builder_finish(int64_t handle) {
    RtStringBuilder* builder = rt_string_builder_from_handle(handle);
    if (!builder) return rt_core_nil();
    int64_t result = rt_string_new(builder->data, (uint64_t)builder->len);
    builder->magic = 0;
    free(builder->data);
    free(builder);
    return result;
}

int64_t rt_string_builder_len(int64_t handle) {
    RtStringBuilder* builder = rt_string_builder_from_handle(handle);
    return builder ? (int64_t)builder->len : -1;
}

void rt_string_builder_free(int64_t handle) {
    RtStringBuilder* builder = rt_string_builder_from_handle(handle);
    if (!builder) return;
    builder->magic = 0;
    free(builder->data);
    free(builder);
}

/* Bug #136: string-interpolation operand coercion to a raw C string.
 * Interpolation `{expr}` operands are MIXED and statically undiscriminable:
 * a tagged heap string (e.g. an argv element built via rt_string_new) vs a
 * raw char* (e.g. a bootstrap string literal returned from a function). This
 * inspects the tag at runtime: a valid tagged string yields its null-
 * terminated buffer; anything else above the hosted low-address guard is
 * assumed to already be a raw char* and passed through. Used by MIR StringLit
 * interpolation lowering, which then
 * concatenates the raw segments with rt_strcat. Uses the same rt_core_as_string
 * accessor + s->data buffer as rt_string_data above. */
const char* rt_interp_cstr(int64_t v) {
    RtCoreString* s = rt_core_as_string(v);
    if (!s && v < 0x10000) return NULL;
    return s ? (const char*)s->data : (const char*)(uintptr_t)v;
}

/* Scan for the first non-ASCII byte. Returns the byte offset of the first byte
 * >= 0x80, or `len` when the whole buffer is ASCII. Word-at-a-time so the
 * common all-ASCII document costs ~len/8 iterations rather than len. */
static uint64_t rt_str_first_non_ascii(const uint8_t* data, uint64_t len) {
    uint64_t i = 0;
    while (i + 8 <= len) {
        uint64_t w;
        memcpy(&w, data + i, 8);
        if (w & 0x8080808080808080ULL) break;
        i += 8;
    }
    while (i < len && data[i] < 0x80) i++;
    return i;
}

/* Return the Unicode code point at character index `index`.
 *
 * SEMANTICS ARE UNCHANGED: `index` is a CHARACTER (codepoint) index, exactly as
 * before. Only the cost changed.
 *
 * The old body walked UTF-8 from byte 0 on every call, making this O(index) and
 * turning every `while i < s.len(): s.char_code_at(i)` loop in the codebase into
 * O(n^2). Within an ASCII prefix a character index IS a byte index, so we can
 * answer directly out of the buffer:
 *
 *   - flag cached  -> O(1) direct byte read.
 *   - else scan for the first non-ASCII byte:
 *       none in the string   -> whole string is ASCII, cache the flag, O(1) read
 *       first one is past    -> `index` still sits in the ASCII prefix, O(1) read
 *       first one is at/before -> fall back to the exact original decode walk.
 *
 * The fallback is never reached without having already paid <= the cost the old
 * code paid, so no input gets slower. The cached flag is sound because Simple
 * strings are immutable and the flag is positive-only (set => proven ASCII;
 * unset => unknown), so a missed cache only costs a rescan, never a wrong answer.
 *
 * NOTE: deliberately does NOT touch the cp-count field (bits [29:0]). That field
 * overlaps RT_CORE_STRING_FLAG_SHARED at bit 0, so writing a cp-count would clear
 * the SHARED bit and defeat rt_string_free's refusal to free interned literals.
 * See the report accompanying this change. */
int64_t rt_string_char_code_at(int64_t string, int64_t index) {
    RtCoreString* s = rt_core_as_string(string);
    const uint8_t* data;
    uint64_t len;
    uint64_t byte_index = 0;
    uint64_t char_index = 0;
    if (index < 0) return 0;
    if (s) {
        data = (const uint8_t*)s->data;
        len = s->len;
    } else {
        data = (const uint8_t*)(uintptr_t)string;
        if (!data) return 0;
        len = strlen((const char*)data);
    }
    if ((uint64_t)index >= len) {
        /* Byte length bounds the character count, so an index at or past it can
         * only resolve inside a multi-byte string; let the walk decide (it
         * returns 0 when the index is genuinely out of range). */
        if (s && (s->reserved & SIMD_CACHE_FLAG_IS_ASCII)) return 0;
    } else if (s && (s->reserved & SIMD_CACHE_FLAG_IS_ASCII)) {
        return data[index];
    } else {
        uint64_t first_hi = rt_str_first_non_ascii(data, len);
        if (first_hi == len) {
            /* Whole string is ASCII: char index == byte index, now and forever. */
            if (s) s->reserved |= SIMD_CACHE_FLAG_IS_ASCII;
            return data[index];
        }
        if (first_hi > (uint64_t)index) {
            /* `index` lies strictly inside the ASCII prefix. */
            return data[index];
        }
        /* Multi-byte content at or before `index`: fall through to the walk. */
    }
    while (byte_index < len) {
        uint8_t b0 = data[byte_index];
        uint64_t width = 1;
        int64_t code = b0;
        if (b0 >= 194 && b0 <= 223 && byte_index + 1 < len) {
            width = 2;
            code = ((int64_t)(b0 & 31) << 6) | (data[byte_index + 1] & 63);
        } else if (b0 >= 224 && b0 <= 239 && byte_index + 2 < len) {
            width = 3;
            code = ((int64_t)(b0 & 15) << 12) | ((int64_t)(data[byte_index + 1] & 63) << 6) | (data[byte_index + 2] & 63);
        } else if (b0 >= 240 && b0 <= 244 && byte_index + 3 < len) {
            width = 4;
            code = ((int64_t)(b0 & 7) << 18) | ((int64_t)(data[byte_index + 1] & 63) << 12) | ((int64_t)(data[byte_index + 2] & 63) << 6) | (data[byte_index + 3] & 63);
        }
        if (char_index == (uint64_t)index) return code;
        byte_index += width;
        char_index += 1;
    }
    return 0;
}

int64_t __simple_rt_string_char_code_at(int64_t string, int64_t index) {
    return rt_string_char_code_at(string, index);
}

/* Return the raw BYTE at BYTE index `index`, or 0 if out of range.
 *
 * Deliberately NOT rt_string_char_code_at: that one is CHARACTER-indexed and
 * the two disagree on any non-ASCII text ("café,".byte_at(3) is 195, the
 * 0xC3 lead byte, while char_code_at(3) is 233 for 'é'). Byte-framing callers
 * (e.g. the web renderer's browser_renderer_protocol.spl scanning for byte
 * 10 '\n' / 44 ',') index the raw UTF-8 buffer directly, so a character
 * index would desync the frame at the first multi-byte codepoint.
 * O(1): straight buffer read, no codepoint walk needed. */
int64_t rt_string_byte_at(int64_t string, int64_t index) {
    RtCoreString* s = rt_core_as_string(string);
    const uint8_t* data;
    uint64_t len;
    if (index < 0) return 0;
    if (s) {
        data = (const uint8_t*)s->data;
        len = s->len;
    } else {
        data = (const uint8_t*)(uintptr_t)string;
        if (!data) return 0;
        len = strlen((const char*)data);
    }
    if ((uint64_t)index >= len) return 0;
    return data[index];
}

int64_t __simple_rt_string_byte_at(int64_t string, int64_t index) {
    return rt_string_byte_at(string, index);
}

int64_t rt_string_char_at(int64_t string, int64_t index) {
    RtCoreString* s = rt_core_as_string(string);
    if (!s || index < 0 || (uint64_t)index >= s->len) return rt_core_nil();
    return rt_string_new((const uint8_t*)s->data + index, 1);
}

int64_t rt_string_concat(int64_t left, int64_t right) {
    RtCoreString* a = rt_core_as_string(left);
    RtCoreString* b = rt_core_as_string(right);
    int64_t left_text = left;
    int64_t right_text = right;
    if (!a) {
        left_text = rt_to_string(left);
        a = rt_core_as_string(left_text);
    }
    if (!b) {
        right_text = rt_to_string(right);
        b = rt_core_as_string(right_text);
    }
    if (!a || !b) return rt_core_nil();

    /* a->len + b->len can wrap uint64_t for adversarial/corrupt inputs. A
     * wrapped small `len` still succeeds malloc (so the `!out` check below
     * never fires) but the memcpy calls below still copy the ORIGINAL
     * un-wrapped a->len/b->len bytes, writing far past the undersized
     * allocation and corrupting whatever heap object follows it. Reject
     * loudly via the file's established unrecoverable-error convention
     * (spl_panic, see rt_panic/panic above) instead of truncating or
     * returning a plausible-looking nil. */
    if (a->len > UINT64_MAX - b->len) {
        spl_panic("rt_string_concat: length overflow");
    }
    uint64_t len = a->len + b->len;
    RtCoreString* out = (RtCoreString*)malloc(sizeof(RtCoreString) + (size_t)len + 1);
    if (!out) return rt_core_nil();
    out->kind = RT_VALUE_HEAP_STRING;
    out->reserved = 0;
    out->len = len;
    if (a->len > 0) memcpy(out->data, a->data, (size_t)a->len);
    if (b->len > 0) memcpy(out->data + a->len, b->data, (size_t)b->len);
    out->data[len] = '\0';
    if (!rt_core_register_string(out)) {
        free(out);
        return rt_core_nil();
    }
    return (int64_t)(((uint64_t)(uintptr_t)out) | RT_VALUE_TAG_HEAP);
}

/// Runtime dispatch for `any + any`: if either operand is a heap string, perform
/// string concatenation; otherwise perform integer arithmetic addition.
/// This matches the interpreter's BinOp::Add behaviour for ANY-typed operands.
int64_t rt_any_add(int64_t left, int64_t right) {
    if (rt_core_as_string(left) || rt_core_as_string(right)) {
        return rt_string_concat(left, right);
    }
    return left + right;
}

int64_t rt_len(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (s) return (int64_t)s->len;
    RtCoreArray* a = rt_core_as_array(value);
    return a ? a->len : 0;
}

/* Defined further below in this file; declared here so rt_to_string's float
 * arm can share the one correct f64 renderer. */
int64_t rt_raw_f64_to_string(double v);

/* Aggregate formatters for rt_to_string (Batch B / bugs #3 #4 #5 #6, see
 * doc/08_tracking/bug/pure_simple_fix_plan_2026-07-29.md). Each returns a
 * fresh rt_string_new handle. Defined below (after rt_to_string) since they
 * recurse into it; forward-declared here so rt_to_string's dispatch can call
 * them. */
static int64_t rt_core_format_array_like(RtCoreArray* array, int is_tuple);
static int64_t rt_core_format_dict(RtCoreDict* dict);
static int64_t rt_core_format_enum(RtCoreEnum* e);

int64_t rt_to_string(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (s) return value;

    /* Aggregate dispatch: only registered heap objects with a recognized
     * kind are handled; anything else (including a raw i64 that merely
     * aliases the HEAP tag bits) falls through to the existing scalar/opaque
     * paths below, exactly as before -- rt_core_as_registered_array,
     * rt_core_as_dict, and rt_core_as_enum all gate on registry membership
     * (a pure pointer compare) before ever dereferencing, so this cannot
     * mis-decode a non-heap value. */
    RtCoreArray* agg_array = rt_core_as_registered_array(value);
    if (agg_array) {
        return rt_core_format_array_like(agg_array, (agg_array->flags & RT_CORE_ARRAY_FLAG_TUPLE) != 0);
    }
    RtCoreDict* agg_dict = rt_core_as_dict(value);
    if (agg_dict) {
        return rt_core_format_dict(agg_dict);
    }
    RtCoreEnum* agg_enum = rt_core_as_enum(value);
    if (agg_enum) {
        /* rt_core_format_enum returns rt_core_nil() for a custom user enum
         * (no name metadata reaches the runtime -- see its comment); fall
         * through to the opaque <value:0x..> marker below rather than
         * return nil as if that were the formatted text. */
        int64_t enum_str = rt_core_format_enum(agg_enum);
        if (enum_str != rt_core_nil()) return enum_str;
    }

    char buf[64];
    if (rt_core_is_int(value)) {
        /* ARITHMETIC shift: a boxed negative int is stored as (v << 3), so the
         * unbox must sign-extend. A logical >>3 rendered boxed -1 as
         * 2305843009213693951 (== (uint64_t)-1 >> 3) -- see rt_core_as_int. */
        int64_t n = rt_core_as_int(value);
        int len = snprintf(buf, sizeof(buf), "%lld", (long long)n);
        return rt_string_new((const uint8_t*)buf, len > 0 ? (uint64_t)len : 0);
    }
    {   /* Heap-boxed float (the LOSSLESS form rt_value_float produces): read the
         * stored double. Must precede the legacy inline decode below -- that one
         * masks the tag off the WORD, which for a heap box is the malloc pointer,
         * so a heap float rendered as the pointer bit-cast to a double (a ~1e-313
         * denormal that drifted upward with the heap). See doc/08_tracking/bug/
         * native_lane_prints_every_f64_as_denormal_garbage_2026-08-10.md. */
        RtCoreFloat* boxed = rt_core_as_heap_float(value);
        if (boxed) return rt_raw_f64_to_string(boxed->value);
    }
    if (rt_core_is_float(value)) {
        /* Legacy inline TAG_FLOAT only: payload IS the bit pattern, low 3
         * mantissa bits already zeroed at box time. */
        uint64_t bits = ((uint64_t)value) & ~RT_VALUE_TAG_MASK;
        double f;
        memcpy(&f, &bits, sizeof(f));
        /* Share rt_raw_f64_to_string rather than formatting here: the old
         * "%.17g" rendered 1.0 as "1" (dropping the fraction -- see
         * doc/08_tracking/bug/f64_integral_to_text_drops_fraction_2026-07-25.md)
         * and 0.1 as "0.10000000000000001" (longest, not shortest, round-trip).
         * A tagged/boxed-ANY float must read the same as an unboxed one. */
        return rt_raw_f64_to_string(f);
    }
    if (rt_core_is_special(value)) {
        switch (rt_core_special_payload(value)) {
            case RT_VALUE_SPECIAL_TRUE:
                return rt_string_new((const uint8_t*)"true", 4);
            case RT_VALUE_SPECIAL_FALSE:
                return rt_string_new((const uint8_t*)"false", 5);
            case RT_VALUE_SPECIAL_NIL:
            default:
                return rt_string_new(NULL, 0);
        }
    }
    int len = snprintf(buf, sizeof(buf), "<value:0x%llx>", (unsigned long long)(uint64_t)value);
    return rt_string_new((const uint8_t*)buf, len > 0 ? (uint64_t)len : 0);
}

/* rt_core_format_array_like -- shared tuple/array renderer.
 *
 * Tuples and plain arrays are the exact same RtCoreArray representation
 * (rt_tuple_new is literally rt_array_new, see above), disambiguated only by
 * RT_CORE_ARRAY_FLAG_TUPLE (set at construction in rt_tuple_new). Oracle
 * (SIMPLE_EXECUTION_MODE=interpreter): tuple -> "(a, b, c)", empty tuple ->
 * "()", single-element tuple -> "(5)" (NO trailing comma -- verified via
 * `print (5,)`); array -> "[a, b, c]", empty array -> "[]" (verified via
 * `print [3,1,2].sorted()` -> "[1, 2, 3]"). Elements recurse through
 * rt_to_string so nested aggregates format correctly.
 *
 * Only the plain tagged-ANY element layout (flags without BYTES/U64_PACKED)
 * is recursed through rt_to_string, since only that layout stores actual
 * tagged/boxed values; BYTES stores raw uint8 bytes and U64_PACKED stores
 * raw (untagged) i64 words -- both are internal storage optimizations for
 * specific typed arrays, not ANY-typed element sequences, so each is
 * rendered as a plain decimal integer per element instead. */
static int64_t rt_core_format_array_like(RtCoreArray* array, int is_tuple) {
    int64_t sb = rt_string_builder_new();
    if (!sb) return rt_string_new((const uint8_t*)(is_tuple ? "()" : "[]"), 2);
    rt_string_builder_push(sb, rt_string_new((const uint8_t*)(is_tuple ? "(" : "["), 1));
    int64_t sep = rt_string_new((const uint8_t*)", ", 2);
    for (int64_t i = 0; i < array->len; i++) {
        if (i > 0) rt_string_builder_push(sb, sep);
        char raw_buf[32];
        int64_t elem_str;
        if (array->flags & RT_CORE_ARRAY_FLAG_BYTES) {
            int rl = snprintf(raw_buf, sizeof(raw_buf), "%d", (int)((uint8_t*)array->data)[i]);
            elem_str = rt_string_new((const uint8_t*)raw_buf, rl > 0 ? (uint64_t)rl : 0);
        } else if (array->flags & RT_CORE_ARRAY_FLAG_U64_PACKED) {
            int rl = snprintf(raw_buf, sizeof(raw_buf), "%lld", (long long)((int64_t*)array->data)[i]);
            elem_str = rt_string_new((const uint8_t*)raw_buf, rl > 0 ? (uint64_t)rl : 0);
        } else {
            elem_str = rt_to_string(((int64_t*)array->data)[i]);
        }
        rt_string_builder_push(sb, elem_str);
    }
    rt_string_builder_push(sb, rt_string_new((const uint8_t*)(is_tuple ? ")" : "]"), 1));
    return rt_string_builder_finish(sb);
}

/* rt_core_format_dict -- Oracle (interpreter): "{k: v, ...}", entries sorted
 * ascending by their RENDERED key string (byte-wise, not numeric -- verified:
 * a Dict<i64,text> with keys 1, 10, 2 prints "{1: x, 10: y, 2: z}", the same
 * order "1" < "10" < "2" sorts as plain strings), bare/unquoted keys and
 * values (verified: {"a": "hello"} prints "{a: hello}", no quotes anywhere),
 * empty dict -> "{}". Keys/values recurse through rt_to_string. */
typedef struct RtCoreDictSortEntry {
    int64_t key_str;   /* rendered key, tagged rt_string handle */
    int64_t value;     /* raw tagged value, rendered lazily during emit */
} RtCoreDictSortEntry;

static int rt_core_dict_sort_entry_less(int64_t a_str, int64_t b_str) {
    RtCoreString* a = rt_core_as_string(a_str);
    RtCoreString* b = rt_core_as_string(b_str);
    if (!a || !b) return 0;
    uint64_t min_len = a->len < b->len ? a->len : b->len;
    int cmp = min_len > 0 ? memcmp(a->data, b->data, (size_t)min_len) : 0;
    if (cmp != 0) return cmp < 0;
    return a->len < b->len;
}

static int64_t rt_core_format_dict(RtCoreDict* dict) {
    int64_t n = dict->len;
    if (n <= 0) return rt_string_new((const uint8_t*)"{}", 2);
    RtCoreDictSortEntry* entries = (RtCoreDictSortEntry*)malloc((size_t)n * sizeof(RtCoreDictSortEntry));
    if (!entries) return rt_string_new((const uint8_t*)"{}", 2);
    int64_t out_i = 0;
    for (int64_t i = 0; i < dict->cap && out_i < n; i++) {
        if (dict->entries[i].occupied != 1) continue;
        entries[out_i].key_str = rt_to_string(dict->entries[i].key);
        entries[out_i].value = dict->entries[i].value;
        out_i++;
    }
    /* Insertion sort: dict print sizes are small in practice and this keeps
     * the comparator a plain function (no qsort_r portability concerns). */
    for (int64_t i = 1; i < out_i; i++) {
        RtCoreDictSortEntry cur = entries[i];
        int64_t j = i - 1;
        while (j >= 0 && rt_core_dict_sort_entry_less(cur.key_str, entries[j].key_str)) {
            entries[j + 1] = entries[j];
            j--;
        }
        entries[j + 1] = cur;
    }
    int64_t sb = rt_string_builder_new();
    if (!sb) {
        free(entries);
        return rt_string_new((const uint8_t*)"{}", 2);
    }
    rt_string_builder_push(sb, rt_string_new((const uint8_t*)"{", 1));
    int64_t sep = rt_string_new((const uint8_t*)", ", 2);
    int64_t colon = rt_string_new((const uint8_t*)": ", 2);
    for (int64_t i = 0; i < out_i; i++) {
        if (i > 0) rt_string_builder_push(sb, sep);
        rt_string_builder_push(sb, entries[i].key_str);
        rt_string_builder_push(sb, colon);
        rt_string_builder_push(sb, rt_to_string(entries[i].value));
    }
    free(entries);
    rt_string_builder_push(sb, rt_string_new((const uint8_t*)"}", 1));
    return rt_string_builder_finish(sb);
}

/* rt_core_format_enum -- Option/Result formatting ONLY.
 *
 * IMPORTANT LIMITATION (see report to parent): enum_id 0 and 1 are reserved
 * compiler constants for Result and Option respectively (see rt_enum_new's
 * comment above), so those two are safe to name here. Every OTHER enum_id is
 * a per-declared-type numeric identity assigned by the compiler's
 * enum_runtime_id_index (switch_operators_calls.spl) -- but that name table
 * (enum type name, variant names) is never emitted into the runtime binary
 * as data, so the C runtime has no way to recover "Color"/"Green" etc. for a
 * user-defined enum. Fabricating a plausible-looking but wrong name would be
 * worse than the existing opaque fallback, so custom enums intentionally
 * fall through to rt_to_string's <value:0x..> fallback unchanged. Oracle
 * verified via SIMPLE_EXECUTION_MODE=interpreter: Option::Some(3) ->
 * "Option::Some(3)", None -> "Option::None", Result Ok(7) -> "Result::Ok(7)",
 * Err("bad") -> "Result::Err(bad)". Returns rt_core_nil() to signal "not
 * handled, fall through" (nil is never a real formatted string result). */
static int64_t rt_core_format_enum(RtCoreEnum* e) {
    int64_t id = (int64_t)e->enum_id;
    int64_t disc = (int64_t)e->discriminant;
    if (id == 1) {
        /* Option: discriminant 0 = Some(payload), 1 = None (see
         * ensure_option_handle in switch_operators_calls.spl). */
        if (disc == 1) return rt_string_new((const uint8_t*)"Option::None", 12);
        int64_t sb = rt_string_builder_new();
        rt_string_builder_push(sb, rt_string_new((const uint8_t*)"Option::Some(", 13));
        rt_string_builder_push(sb, rt_to_string(e->payload));
        rt_string_builder_push(sb, rt_string_new((const uint8_t*)")", 1));
        return rt_string_builder_finish(sb);
    }
    if (id == 0) {
        /* Result: discriminant 0 = Ok(payload), 1 = Err(payload) (see
         * lower_try_expr's docstring in switch_operators_calls.spl). */
        int64_t sb = rt_string_builder_new();
        if (disc == 1) {
            rt_string_builder_push(sb, rt_string_new((const uint8_t*)"Result::Err(", 12));
        } else {
            rt_string_builder_push(sb, rt_string_new((const uint8_t*)"Result::Ok(", 11));
        }
        rt_string_builder_push(sb, rt_to_string(e->payload));
        rt_string_builder_push(sb, rt_string_new((const uint8_t*)")", 1));
        return rt_string_builder_finish(sb);
    }
    /* Custom user enum: no name metadata reaches the runtime -- fall through
     * (caller must treat rt_core_nil() as "not handled"). */
    return rt_core_nil();
}

int64_t rt_raw_u64_to_string(int64_t raw) {
    char buf[32];
    int len = snprintf(buf, sizeof(buf), "%llu", (unsigned long long)(uint64_t)raw);
    return rt_string_new((const uint8_t*)buf, len > 0 ? (uint64_t)len : 0);
}

int64_t rt_raw_i64_to_string(int64_t raw) {
    char buf[32];
    /* %lld handles INT64_MIN correctly (no manual negation needed). */
    int len = snprintf(buf, sizeof(buf), "%lld", (long long)raw);
    return rt_string_new((const uint8_t*)buf, len > 0 ? (uint64_t)len : 0);
}

/* rt_opt_i64_to_string / rt_opt_bool_to_string / rt_opt_f64_to_string — P1
 * fix (2026-07-22), C-runtime parity mirrors of the Cranelift-path helpers
 * added in compiler_rust/runtime/src/value/sffi/io_print.rs (see that file
 * for the full representation rationale). A flat optional (`i64?`/`bool?`/
 * `f64?`) lowers to HirType::Pointer{inner} and is represented at runtime as
 * a RAW payload carrying either the bare inner value or the nil sentinel
 * (rt_core_nil() == 3) -- never a tagged RuntimeValue. NOT YET WIRED to any
 * C-backend call site here (the self-hosted .spl compiler's own print
 * lowering lives in switch_operators_calls.spl, out of scope for this
 * change) -- added for parity with the existing rt_raw_i64_to_string /
 * rt_raw_bool_to_string / rt_raw_f64_to_string pattern only. See
 * doc/08_tracking/bug/interp_index_of_digit_leading_literal_2026-07-22.md.
 */
/* Forward decl: rt_raw_f64_to_string is defined further below in this file. */
int64_t rt_raw_f64_to_string(double v);

int64_t rt_opt_i64_to_string(int64_t raw) {
    if (raw == rt_core_nil()) return rt_string_new((const uint8_t*)"nil", 3);
    char buf[32];
    int len = snprintf(buf, sizeof(buf), "%lld", (long long)raw);
    return rt_string_new((const uint8_t*)buf, len > 0 ? (uint64_t)len : 0);
}

int64_t rt_opt_bool_to_string(int64_t raw) {
    if (raw == rt_core_nil()) return rt_string_new((const uint8_t*)"nil", 3);
    if (raw != 0) return rt_string_new((const uint8_t*)"true", 4);
    return rt_string_new((const uint8_t*)"false", 5);
}

int64_t rt_opt_f64_to_string(int64_t raw) {
    if (raw == rt_core_nil()) return rt_string_new((const uint8_t*)"nil", 3);
    double v;
    memcpy(&v, &raw, sizeof(double));
    return rt_raw_f64_to_string(v);
}

/* rt_raw_bool_to_string — same "raw operand, no tag check" contract as
 * rt_raw_i64_to_string (see its callers in switch_operators_calls.spl's
 * lower_bootstrap_print_call), but for a bool-typed MIR local: those are
 * plain 0/1 i64 values at codegen time (not the tagged RT_VALUE_SPECIAL_*
 * scheme rt_to_string() handles), so routing them through the decimal
 * i64 renderer prints "1"/"0" instead of "true"/"false" (native print(bool)
 * divergence from the oracle). Render the raw 0/1 directly as text.
 */
int64_t rt_raw_bool_to_string(int64_t raw) {
    if (raw != 0) return rt_string_new((const uint8_t*)"true", 4);
    return rt_string_new((const uint8_t*)"false", 5);
}

/* rt_raw_f64_to_string — same "raw operand, no tag check" contract as
 * rt_raw_i64_to_string/rt_raw_bool_to_string (see lower_bootstrap_print_call
 * in switch_operators_calls.spl), but for an F64/F32-typed MIR local: the
 * value arrives as an actual `double` (the call-site LLVM arg type is taken
 * from the operand's own MIR type, not from this function's `declare`), NOT
 * a raw i64 bit-pattern -- so this takes `double` directly, not int64_t.
 *
 * Formatting is Python repr()-style: a shortest-round-trip DECIMAL
 * representation (never scientific notation), with a ".0" suffix forced on
 * any integral value. This matches the deployed interpreter oracle for every
 * case where the oracle is correct -- whole/exactly-representable floats keep
 * a trailing ".0" (2.0 -> "2.0", 100.0 -> "100.0", 0.5 -> "0.5", 0.125 ->
 * "0.125") -- and stays correct (round-tripping) where the oracle is provably
 * broken: the oracle prints the 0.1 literal as "0.09999999999999998" (a string
 * that parses to a DIFFERENT double -- it does not round-trip), so native is
 * correct-by-construction with 0.1 -> "0.1", 1.0/3.0 -> "0.3333333333333333"
 * (16 3's). rt_to_string()'s tagged/boxed-ANY float path used to format its own
 * raw %.17g here (0.1 -> "0.10000000000000001", 1.0 -> "1") and did NOT match;
 * it now delegates to this function so boxed and unboxed floats read alike.
 * Algorithm: (1) try the fewest fixed decimal places (0..324) whose %.*f
 * rendering round-trips (strtod) back to the exact same double -- %f (never
 * %e) avoids mismatches like 100.0 -> "1e+02"; (2) if that shortest rendering
 * is integer-looking (no '.', and no letters, so finite -- inf/nan carry
 * letters and pass through untouched), append ".0" (2 -> "2.0", -0 -> "-0.0",
 * 0 -> "0.0"), giving Python-repr float display.
 *
 * Bound 324 (not 17): a tiny-magnitude double needs that many fractional
 * digits before %.*f's fixed-point rendering has enough significant digits
 * to round-trip -- e.g. 1e-100 needs prec=100, and the smallest subnormal
 * (~4.94e-324, right down to DBL_MIN) needs prec=324 (verified by brute-force
 * search over the full double range). The old `<= 17` bound silently fell
 * through to the `prec > 17` fallback for any |v| below ~1e-17, which
 * rendered as "0.00000000000000000" (17 zeros) -- a STRING THAT PARSES BACK
 * TO 0.0, not the original nonzero value: a silent-wrong loss of the entire
 * value, not merely a shortest-vs-longest cosmetic mismatch against the
 * oracle. 1e17-magnitude values and above still resolve at prec=0 (integers
 * at that scale have no fractional part), so raising the bound costs nothing
 * for the common case and only pays for genuinely tiny magnitudes.
 */
int64_t rt_raw_f64_to_string(double v) {
    char buf[512];
    int len = 0;
    int prec;
    /* NaN never round-trips (`NaN == NaN` is false by IEEE754 definition,
     * so the strtod-equality check below can never break the loop early --
     * every one of the 325 iterations would run to no purpose) and glibc's
     * %f ignores precision for it anyway, always rendering the same "nan"/
     * "-nan". Handle it up front: skip the wasted search, and rewrite the
     * libc-lowercase spelling to "NaN"/"-NaN" to match the oracle's actual
     * print output (verified via `bin/simple run` on `0.0/0.0`), which is
     * NOT Python's `repr(float('nan'))` (that's lowercase "nan") -- this
     * oracle is the interpreter, not Python, and its casing is what native
     * must match. */
    if (isnan(v)) {
        len = snprintf(buf, sizeof(buf), "%f", v);
        if (len > 0 && (size_t)len < sizeof(buf)) {
            if (buf[0] == '-' && len >= 4) {
                buf[1] = 'N'; buf[2] = 'a'; buf[3] = 'N';
                len = 4;
            } else if (len >= 3) {
                buf[0] = 'N'; buf[1] = 'a'; buf[2] = 'N';
                len = 3;
            }
        }
        if (len < 0) len = 0;
        return rt_string_new((const uint8_t*)buf, (uint64_t)len);
    }
    /* (1) shortest fixed-point rendering that round-trips exactly. */
    for (prec = 0; prec <= 324; prec++) {
        len = snprintf(buf, sizeof(buf), "%.*f", prec, v);
        if (strtod(buf, NULL) == v) break;
    }
    if (prec > 324) {
        len = snprintf(buf, sizeof(buf), "%.324f", v);
    }
    if (len < 0) len = 0;
    /* (2) force a ".0" on an integer-looking finite value (no '.', no
     * letters). Guard the buffer so the two appended chars + NUL always fit. */
    if (len > 0 && len + 3 < (int)sizeof(buf)) {
        int is_integral = 1;
        for (int i = 0; i < len; i++) {
            char c = buf[i];
            if (c == '.' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')) {
                is_integral = 0;
                break;
            }
        }
        if (is_integral) {
            buf[len] = '.';
            buf[len + 1] = '0';
            buf[len + 2] = '\0';
            len += 2;
        }
    }
    return rt_string_new((const uint8_t*)buf, (uint64_t)len);
}

int64_t rt_value_to_string(int64_t value) {
    return rt_to_string(value);
}

/* SIMD profile externs: the native C bundle previously had NO impls (they
 * lived only in the Rust seed runtime, simd.rs), so any native binary whose
 * closure pulls std.simd (e.g. std.common.encoding.utf8's Utf8Provider) died
 * at link with `undefined symbol: rt_simd_detect_profile`.
 * Only the two symbols with no other C definition live here — the five
 * rt_simd_has_* predicates are REAL cpuid/hwcap detection in
 * runtime_simd_dispatch.c, which is in this same archive; defining stubs
 * for them here made the stage4 archive core define each twice (link error
 * "Stage4 archive core defines `rt_simd_has_avx` 2 times").
 * The profile must agree with those predicates.  A scalar profile on an AVX2,
 * NEON, or RVV host silently disables safe dispatched backends and makes
 * capability/evidence receipts contradict one another.  Tier codes follow
 * std.simd: 0=scalar, 1=x86 SSE2, 2=x86 AVX2, 4=AArch64 NEON, 7=RVV. */
int64_t rt_simd_detect_profile(void) {
    if (rt_simd_has_avx2()) return 2;
    if (rt_simd_has_sse()) return 1;
    if (rt_simd_has_neon()) return 4;
    if (rt_simd_has_rvv()) return 7;
    return 0;
}
int64_t rt_simd_profile_name(void) {
    int64_t profile = rt_simd_detect_profile();
    static const uint8_t avx2_name[] = "x86_64_avx2";
    static const uint8_t sse2_name[] = "x86_64_sse2";
    static const uint8_t neon_name[] = "aarch64_neon";
    static const uint8_t rvv_name[] = "riscv64_rvv";
    static const uint8_t scalar_name[] = "scalar";
    if (profile == 2) return rt_string_new(avx2_name, 11);
    if (profile == 1) return rt_string_new(sse2_name, 11);
    if (profile == 4) return rt_string_new(neon_name, 12);
    if (profile == 7) return rt_string_new(rvv_name, 11);
    return rt_string_new(scalar_name, 6);
}

typedef struct RtCoreEqPair {
    RtCoreArray* left;
    RtCoreArray* right;
} RtCoreEqPair;

#define RT_CORE_EQ_MAX_ARRAY_PAIRS 256

static int rt_core_value_eq_inner(
    int64_t left,
    int64_t right,
    RtCoreEqPair* visited,
    size_t visited_len);

static int rt_core_generic_int_eq(int64_t value, int64_t expected) {
    RtCoreUInt* u = rt_core_as_heap_uint(value);
    int64_t signed_value = rt_core_is_int(value) ? rt_core_as_int(value) : -1;
    return (rt_core_is_int(value) && expected >= 0 && signed_value >= 0 && signed_value == expected) ||
        (u && expected >= 0 && u->value == (uint64_t)expected);
}

static int rt_core_array_eq(
    RtCoreArray* left,
    RtCoreArray* right,
    RtCoreEqPair* visited,
    size_t visited_len) {
    if (left == right) return 1;
    if (!left || !right || left->len != right->len) return 0;
    for (size_t i = 0; i < visited_len; i++) {
        if (visited[i].left == left && visited[i].right == right) return 1;
    }
    if (visited_len >= RT_CORE_EQ_MAX_ARRAY_PAIRS) return 0;
    visited[visited_len++] = (RtCoreEqPair){left, right};

    int left_bytes = (left->flags & RT_CORE_ARRAY_FLAG_BYTES) != 0;
    int right_bytes = (right->flags & RT_CORE_ARRAY_FLAG_BYTES) != 0;
    int left_u64 = (left->flags & RT_CORE_ARRAY_FLAG_U64_PACKED) != 0;
    int right_u64 = (right->flags & RT_CORE_ARRAY_FLAG_U64_PACKED) != 0;
    if (left_bytes && right_bytes) {
        return left->len == 0 || memcmp(left->data, right->data, (size_t)left->len) == 0;
    }
    if (left_u64 && right_u64) {
        return left->len == 0 ||
            memcmp(left->data, right->data, (size_t)left->len * sizeof(uint64_t)) == 0;
    }

    for (int64_t i = 0; i < left->len; i++) {
        if (left_bytes) {
            int64_t value = (int64_t)((uint8_t*)left->data)[i];
            if (right_u64) {
                if ((uint64_t)value != ((uint64_t*)right->data)[i]) return 0;
            } else if (!rt_core_generic_int_eq(((int64_t*)right->data)[i], value)) {
                return 0;
            }
        } else if (right_bytes) {
            int64_t value = (int64_t)((uint8_t*)right->data)[i];
            if (left_u64) {
                if (((uint64_t*)left->data)[i] != (uint64_t)value) return 0;
            } else if (!rt_core_generic_int_eq(((int64_t*)left->data)[i], value)) {
                return 0;
            }
        } else if (left_u64) {
            if (!rt_core_generic_int_eq(
                    ((int64_t*)right->data)[i],
                    (int64_t)((uint64_t*)left->data)[i])) return 0;
        } else if (right_u64) {
            if (!rt_core_generic_int_eq(
                    ((int64_t*)left->data)[i],
                    (int64_t)((uint64_t*)right->data)[i])) return 0;
        } else if (!rt_core_value_eq_inner(
                       ((int64_t*)left->data)[i],
                       ((int64_t*)right->data)[i],
                       visited,
                       visited_len)) {
            return 0;
        }
    }
    return 1;
}

static int rt_core_enum_eq(
    RtCoreEnum* left,
    RtCoreEnum* right,
    RtCoreEqPair* visited,
    size_t visited_len) {
    return left && right && left->enum_id == right->enum_id &&
        left->discriminant == right->discriminant &&
        rt_core_value_eq_inner(left->payload, right->payload, visited, visited_len);
}

static int rt_core_value_eq_inner(
    int64_t left,
    int64_t right,
    RtCoreEqPair* visited,
    size_t visited_len) {
    if (left == right) return 1;
    if (rt_core_is_float(left) || rt_core_is_float(right)) {
        return rt_core_is_float(left) && rt_core_is_float(right) &&
            rt_core_as_float(left) == rt_core_as_float(right);
    }
    RtCoreUInt* left_uint = rt_core_as_heap_uint(left);
    RtCoreUInt* right_uint = rt_core_as_heap_uint(right);
    if (left_uint || right_uint) {
        if (left_uint && right_uint) return left_uint->value == right_uint->value;
        if (left_uint && rt_core_is_int(right)) {
            int64_t signed_right = rt_core_as_int(right);
            return signed_right >= 0 && left_uint->value == (uint64_t)signed_right;
        }
        if (right_uint && rt_core_is_int(left)) {
            int64_t signed_left = rt_core_as_int(left);
            return signed_left >= 0 && (uint64_t)signed_left == right_uint->value;
        }
        return 0;
    }
    if (rt_core_is_special(left) || rt_core_is_special(right)) return 0;
    RtCoreString* a = rt_core_as_string(left);
    RtCoreString* b = rt_core_as_string(right);
    if (a || b) {
        if (!a || !b || a->len != b->len) return 0;
        return a->len == 0 || memcmp(a->data, b->data, (size_t)a->len) == 0;
    }
    RtCoreArray* left_array = rt_core_as_registered_array(left);
    RtCoreArray* right_array = rt_core_as_registered_array(right);
    if (left_array || right_array) {
        return rt_core_array_eq(left_array, right_array, visited, visited_len);
    }
    RtCoreEnum* left_enum = rt_core_as_registered_enum(left);
    RtCoreEnum* right_enum = rt_core_as_registered_enum(right);
    if (left_enum || right_enum) {
        return rt_core_enum_eq(left_enum, right_enum, visited, visited_len);
    }
    return 0;
}

int64_t rt_native_eq(int64_t left, int64_t right) {
    if (left == right) return 1;
    if (rt_core_is_float(left) || rt_core_is_float(right)) {
        return rt_core_is_float(left) && rt_core_is_float(right) &&
            rt_core_as_float(left) == rt_core_as_float(right);
    }
    RtCoreUInt* left_uint = rt_core_as_heap_uint(left);
    RtCoreUInt* right_uint = rt_core_as_heap_uint(right);
    if (left_uint || right_uint) {
        if (left_uint && right_uint) return left_uint->value == right_uint->value;
        if (left_uint && rt_core_is_int(right)) {
            int64_t signed_right = rt_core_as_int(right);
            return signed_right >= 0 && left_uint->value == (uint64_t)signed_right;
        }
        if (right_uint && rt_core_is_int(left)) {
            int64_t signed_left = rt_core_as_int(left);
            return signed_left >= 0 && (uint64_t)signed_left == right_uint->value;
        }
        return 0;
    }
    if (rt_core_is_special(left) || rt_core_is_special(right)) return 0;
    RtCoreString* left_string = rt_core_as_string(left);
    RtCoreString* right_string = rt_core_as_string(right);
    if (left_string || right_string) {
        if (!left_string || !right_string || left_string->len != right_string->len) return 0;
        return left_string->len == 0 ||
            memcmp(left_string->data, right_string->data, (size_t)left_string->len) == 0;
    }
    RtCoreArray* left_array = rt_core_as_registered_array(left);
    RtCoreArray* right_array = rt_core_as_registered_array(right);
    RtCoreEnum* left_enum = rt_core_as_registered_enum(left);
    RtCoreEnum* right_enum = rt_core_as_registered_enum(right);
    if (!left_array && !right_array && !left_enum && !right_enum) return 0;

    RtCoreEqPair visited[RT_CORE_EQ_MAX_ARRAY_PAIRS];
    if (left_array || right_array) {
        return rt_core_array_eq(left_array, right_array, visited, 0);
    }
    return rt_core_enum_eq(left_enum, right_enum, visited, 0);
}

int64_t rt_string_eq(int64_t left, int64_t right) {
    RtCoreString* a = rt_core_as_string(left);
    RtCoreString* b = rt_core_as_string(right);
    if (!a || !b || a->len != b->len) return 0;
    return a->len == 0 || memcmp(a->data, b->data, (size_t)a->len) == 0;
}

int64_t rt_text_eq_fast(int64_t left, int64_t right) {
    return rt_string_eq(left, right);
}

/* #148: native-path `text == text` / `text != text` equality.
 *
 * On the normal native (non-bootstrap) MIR->LLVM path a "str"-typed MIR local
 * (mir_type_is_str) can be materialized as EITHER representation, and the two
 * are statically undiscriminable at compile time:
 *   - a TAGGED heap-string handle (built by rt_string_new -- e.g. argv
 *     elements from rt_cli_get_args/rt_get_args), or
 *   - a RAW char* pointer (a getelementptr into a `[N x i8]` global -- e.g. a
 *     bare string literal `"hello"`, per emit_bootstrap_str_const).
 *
 * Before this fix, `a == "hello"` lowered to a plain `icmp eq i64` on the two
 * operands as opaque integers: a tagged handle (a heap pointer OR'd with
 * RT_VALUE_TAG_HEAP) can never numerically equal a raw string-literal
 * pointer, so the comparison always failed regardless of content (pointer
 * identity, not content -- see MIR lowering's Eq/Ne binop intercept in
 * expr_dispatch.spl, which now routes here whenever local_is_str() says
 * either operand is string-shaped).
 *
 * Root fix: normalize BOTH operands to a raw null-terminated buffer via the
 * same tagged-or-raw runtime detection rt_interp_cstr already uses for
 * string-interpolation operands (bug #136), then compare byte content. This
 * handles all four combinations (tagged/tagged, tagged/raw, raw/tagged,
 * raw/raw) without any compile-time guess about which side is which --
 * unlike rt_string_eq/rt_native_eq above, which require BOTH sides already
 * tagged and so silently return 0 (never equal) for a raw literal operand. */
int64_t rt_text_eq_any(int64_t left, int64_t right) {
    /* Flat-Option nil sentinel awareness (RT_NIL == 3). A `Dict<_,text>.get(k)`
     * MISS hands back the flat nil sentinel preserved around the decode
     * (dict_get_preserve_flat_nil, 50.mir), and `x == nil` on that str-typed
     * result lowers straight here as rt_text_eq_any(x, 3): NilLit materializes
     * as the raw word 3. The rt_interp_cstr calls below decode the sentinel to
     * NULL, so the `!a || !b` guard used to answer NOT-EQUAL unconditionally --
     * a text-dict miss could never compare equal to nil (bug
     * native_dict_get_miss_returns_zero_not_nil_2026-07-28, residual text row;
     * selfcheck: src/runtime/test/rt_text_eq_any_nil_sentinel_selfcheck.c).
     * nil == nil is EQUAL; nil vs any real string is NOT. */
    if (left == rt_core_nil() || right == rt_core_nil()) return left == right ? 1 : 0;
    const char* a = rt_interp_cstr(left);
    const char* b = rt_interp_cstr(right);
    if (!a || !b) return 0;
    if (a == b) return 1;
    return strcmp(a, b) == 0 ? 1 : 0;
}

int64_t rt_native_neq(int64_t left, int64_t right) {
    return !rt_native_eq(left, right);
}

/* Task #178 (text3 lane): backs native `<`/`<=`/`>`/`>=` on text operands.
 * MIR lowering routes text ordering here (like Eq/NotEq's rt_text_eq_any
 * above, added for bug #148). Previously the frontend did not special-case
 * ordering ops for strings, so a `ptr`-typed operand fell straight through
 * to a raw `icmp slt/sle/sgt/sge ptr, ptr`, comparing the strings' memory
 * ADDRESSES instead of their lexicographic content (observed:
 * `"foo" < "bar"` native said true, oracle interpreter said false --
 * whichever literal happened to be malloc'd/placed at the lower address
 * "won", entirely unrelated to alphabetical order). Same tagged-or-raw
 * normalization as rt_text_eq_any, then a real byte-wise strcmp. Returns a
 * strcmp-style signed result (the caller compares this against 0 with the
 * requested predicate). */
int64_t rt_text_cmp_any(int64_t left, int64_t right) {
    const char* a = rt_interp_cstr(left);
    const char* b = rt_interp_cstr(right);
    if (!a) a = "";
    if (!b) b = "";
    return (int64_t)strcmp(a, b);
}

/* 2026-08-01: ordering counterpart of rt_native_eq, for `<` `<=` `>` `>=`
 * when codegen cannot statically prove either operand's type.
 *
 * Eq/NotEq have had a tag-aware dynamic fallback (rt_native_eq /
 * rt_native_neq) for a long time; the ordering operators did not. Codegen's
 * ordering arm therefore fell through to a raw `icmp` on the two operands as
 * opaque integers whenever static typing was incomplete -- which for a tagged
 * heap string compares its HANDLE ADDRESS, not its content. That is the same
 * class of defect rt_text_cmp_any was introduced to fix for the statically
 * typed case, and it stayed live for the untyped case (observed: a
 * `.substring()` result compared against a `"0"`/`"9"` literal produced
 * address ordering under the JIT, making an ASCII digit-range check return
 * false for most digits). See
 * doc/08_tracking/bug/jit_text_ordering_pointer_compare_2026-08-01.md.
 *
 * Dispatch mirrors rt_native_eq exactly:
 *   - either side a tagged heap string  -> byte-wise strcmp via
 *     rt_text_cmp_any (which additionally normalizes a raw char* literal on
 *     the other side, so tagged/raw mixes work)
 *   - either side a tagged float        -> numeric float compare
 *   - otherwise                         -> raw signed integer compare, which
 *     is what the inline icmp arm would have done
 *
 * Returns a strcmp-style signed result (<0, 0, >0); the caller applies the
 * requested predicate against 0. */
int64_t rt_native_cmp(int64_t left, int64_t right) {
    RtCoreString* left_string = rt_core_as_string(left);
    RtCoreString* right_string = rt_core_as_string(right);
    if (left_string || right_string) {
        return rt_text_cmp_any(left, right);
    }
    if (rt_core_is_float(left) || rt_core_is_float(right)) {
        double a = rt_core_is_float(left) ? rt_core_as_float(left) : (double)left;
        double b = rt_core_is_float(right) ? rt_core_as_float(right) : (double)right;
        if (a < b) return -1;
        if (a > b) return 1;
        return 0;
    }
    if (left < right) return -1;
    if (left > right) return 1;
    return 0;
}

int64_t rt_slice(int64_t value, int64_t start, int64_t end, int64_t step) {
    if (step == 0) return rt_core_nil();

    RtCoreArray* array = rt_core_as_array(value);
    if (array) {
        int64_t len = array->len;
        int64_t begin = start < 0 ? len + start : start;
        int64_t finish = end < 0 ? len + end : end;
        if (begin < 0) begin = 0;
        if (begin > len) begin = len;
        if (finish < 0) finish = 0;
        if (finish > len) finish = len;
        int64_t count = 0;
        for (int64_t i = begin; (step > 0) ? i < finish : i > finish; i += step) count++;
        SplArray* result = (array->flags & RT_CORE_ARRAY_FLAG_BYTES)
            ? rt_byte_array_new((uint64_t)count)
            : ((array->flags & RT_CORE_ARRAY_FLAG_U64_PACKED)
                ? rt_array_new_with_cap_u64(count)
                : rt_array_new(count));
        RtCoreArray* out = rt_core_as_array((int64_t)(uintptr_t)result);
        if (!out) return rt_core_nil();
        for (int64_t i = begin; (step > 0) ? i < finish : i > finish; i += step) {
            if (array->flags & RT_CORE_ARRAY_FLAG_BYTES) {
                ((uint8_t*)out->data)[out->len++] = ((uint8_t*)array->data)[i];
            } else {
                ((int64_t*)out->data)[out->len++] = ((int64_t*)array->data)[i];
            }
        }
        return (int64_t)(uintptr_t)result;
    }

    RtCoreString* s = rt_core_as_string(value);
    if (!s) return rt_core_nil();
    int64_t len = (int64_t)s->len;
    int64_t begin = start;
    int64_t finish = end;
    int64_t stride = step;
    if (begin < 0) begin += len;
    if (finish < 0) finish += len;
    if (begin < 0) begin = 0;
    if (finish < begin) finish = begin;
    if (begin > len) begin = len;
    if (finish > len) finish = len;
    if (stride != 1) {
        uint64_t out_len = 0;
        for (int64_t i = begin; i < finish; i += stride) out_len++;
        RtCoreString* out = (RtCoreString*)malloc(sizeof(RtCoreString) + (size_t)out_len + 1);
        if (!out) return rt_core_nil();
        out->kind = RT_VALUE_HEAP_STRING;
        out->reserved = 0;
        out->len = out_len;
        uint64_t out_i = 0;
        for (int64_t i = begin; i < finish; i += stride) out->data[out_i++] = s->data[i];
        out->data[out_len] = '\0';
        if (!rt_core_register_string(out)) {
            free(out);
            return rt_core_nil();
        }
        return (int64_t)(((uint64_t)(uintptr_t)out) | RT_VALUE_TAG_HEAP);
    }
    /* UTF-8 slice audit, stage 1 (COUNTING ONLY, default off). This range is
     * copied RAW, so a boundary inside a multi-byte codepoint stores invalid
     * bytes and only the byte length betrays it -- stdout's sanitizer renders
     * valid and invalid identically. Record it; do not fail. */
    if (rt_text_slice_audit_level() != 0) {
        rt_text_slice_audit_note(RT_TEXT_SLICE_SITE_RT_SLICE_C, "rt_slice_c",
                                 begin, finish,
                                 (const uint8_t*)s->data, (uint64_t)len,
                                 (const uint8_t*)s->data + begin,
                                 (uint64_t)(finish - begin));
    }
    return rt_string_new((const uint8_t*)s->data + begin, (uint64_t)(finish - begin));
}

int64_t rt_string_starts_with(int64_t value, int64_t prefix) {
    RtCoreString* s = rt_core_as_string(value);
    RtCoreString* p = rt_core_as_string(prefix);
    if (!s || !p || p->len > s->len) return 0;
    return p->len == 0 || memcmp(s->data, p->data, (size_t)p->len) == 0;
}

int64_t rt_string_ends_with(int64_t value, int64_t suffix) {
    RtCoreString* s = rt_core_as_string(value);
    RtCoreString* p = rt_core_as_string(suffix);
    if (!s || !p || p->len > s->len) return 0;
    return p->len == 0 || memcmp(s->data + (s->len - p->len), p->data, (size_t)p->len) == 0;
}

/* Bug (native_chr_builtin_no_lowering, 2026-07-18): `.chr()`/`.to_char()`
 * routes here from both typed and flat-HIR integer lowering, but this symbol
 * was previously absent from the hosted native-build runtime. Semantics match
 * the pure runtime and hardware C owners: a raw Unicode scalar value encoded
 * as UTF-8. Invalid scalar values collapse to the empty string because this
 * ABI layer has no exception mechanism for the interpreter's diagnostic. */
int64_t rt_char_from_code(int64_t code) {
    if (code < 0 || code > 0x10FFFF || (code >= 0xD800 && code <= 0xDFFF)) return rt_string_new(NULL, 0);
    uint32_t cp = (uint32_t)code;
    uint8_t buf[4];
    uint64_t len = 0;
    if (cp < 0x80) {
        buf[len++] = (uint8_t)cp;
    } else if (cp < 0x800) {
        buf[len++] = (uint8_t)(0xC0 | (cp >> 6));
        buf[len++] = (uint8_t)(0x80 | (cp & 0x3F));
    } else if (cp < 0x10000) {
        buf[len++] = (uint8_t)(0xE0 | (cp >> 12));
        buf[len++] = (uint8_t)(0x80 | ((cp >> 6) & 0x3F));
        buf[len++] = (uint8_t)(0x80 | (cp & 0x3F));
    } else {
        buf[len++] = (uint8_t)(0xF0 | (cp >> 18));
        buf[len++] = (uint8_t)(0x80 | ((cp >> 12) & 0x3F));
        buf[len++] = (uint8_t)(0x80 | ((cp >> 6) & 0x3F));
        buf[len++] = (uint8_t)(0x80 | (cp & 0x3F));
    }
    return rt_string_new(buf, len);
}

/* Rust-seed Cranelift emits this legacy helper name for Text.from_char_code.
 * Keep it as a thin ABI alias so Stage-2-produced tools link against the
 * core-C bootstrap runtime, including on macOS arm64. */
int64_t text_dot_from_char_code(int64_t code) {
    return rt_char_from_code(code);
}

int64_t rt_string_find(int64_t value, int64_t needle) {
    RtCoreString* s = rt_core_as_string(value);
    RtCoreString* n = rt_core_as_string(needle);
    if (!s || !n) return -1;
    if (n->len == 0) return 0;
    if (n->len > s->len) return -1;
    for (uint64_t i = 0; i + n->len <= s->len; i++) {
        if (memcmp(s->data + i, n->data, (size_t)n->len) == 0) return (int64_t)i;
    }
    return -1;
}

int64_t rt_text_find(int64_t value, int64_t needle, int64_t start) {
    RtCoreString* s = rt_core_as_string(value);
    RtCoreString* n = rt_core_as_string(needle);
    if (!s || !n) return -1;
    /* Negative start clamps to 0 (the two-arg index_of contract; matches the
     * Rust runtime crate and simple_core impls). */
    if (start < 0) start = 0;
    if (n->len == 0) return start <= (int64_t)s->len ? start : (int64_t)s->len;
    if (start >= (int64_t)s->len || n->len > s->len) return -1;
    for (uint64_t i = (uint64_t)start; i + n->len <= s->len; i++) {
        if (memcmp(s->data + i, n->data, (size_t)n->len) == 0) return (int64_t)i;
    }
    return -1;
}

int64_t rt_string_rfind(int64_t value, int64_t needle) {
    RtCoreString* s = rt_core_as_string(value);
    RtCoreString* n = rt_core_as_string(needle);
    if (!s || !n) return -1;
    if (n->len == 0) return (int64_t)s->len;
    if (n->len > s->len) return -1;
    for (uint64_t i = s->len - n->len + 1; i-- > 0;) {
        if (memcmp(s->data + i, n->data, (size_t)n->len) == 0) return (int64_t)i;
    }
    return -1;
}

int64_t rt_mutex_new(int64_t initial) {
    RtCoreMutex* mutex = (RtCoreMutex*)calloc(1, sizeof(RtCoreMutex));
    if (!mutex) return rt_core_nil();
    mutex->kind = RT_VALUE_HEAP_MUTEX;
    atomic_flag_clear(&mutex->lock);
    mutex->value = initial;
    if (!rt_core_register_mutex(mutex)) {
        free(mutex);
        return rt_core_nil();
    }
    return (int64_t)(((uintptr_t)mutex) | RT_VALUE_TAG_HEAP);
}

int64_t rt_mutex_lock(int64_t handle) {
    RtCoreMutex* mutex = rt_core_as_mutex(handle);
    if (!mutex) return rt_core_nil();
    while (atomic_flag_test_and_set_explicit(&mutex->lock, memory_order_acquire)) { }
    return mutex->value;
}

int64_t rt_mutex_try_lock(int64_t handle) {
    RtCoreMutex* mutex = rt_core_as_mutex(handle);
    if (!mutex || atomic_flag_test_and_set_explicit(&mutex->lock, memory_order_acquire)) {
        return rt_core_nil();
    }
    return mutex->value;
}

int64_t rt_mutex_unlock(int64_t handle, int64_t new_value) {
    RtCoreMutex* mutex = rt_core_as_mutex(handle);
    if (!mutex) return 0;
    mutex->value = new_value;
    atomic_flag_clear_explicit(&mutex->lock, memory_order_release);
    return 1;
}

/* Task #178 (text3 lane): `.contains()` had a frontend extern declaration
 * (types.spl) and a backend LLVM decl (llvm_lib_translate.spl) but NO C
 * implementation anywhere in src/runtime/ -- a genuine missing symbol, not
 * just a missing MIR-lowering case (that gap is fixed separately in
 * method_calls_literals.spl). Both operands are tagged handles by the time
 * this is called (method_calls_literals.spl's erased-receiver fallback tags
 * raw literals first via tag_str_local_if_raw), matching rt_string_find's
 * own contract, so this is a direct wrapper. */
int64_t rt_string_contains(int64_t value, int64_t needle) {
    return rt_string_find(value, needle) >= 0 ? 1 : 0;
}

/* Defined next to rt_string_trim; forward-declared here because
 * rt_string_ascii_case appears earlier in the file. */
static int rt_string_promote_raw_receiver(int64_t value, int64_t* out);

static int64_t rt_string_ascii_case(int64_t value, int to_lower) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) {
        int64_t promoted;
        if (rt_string_promote_raw_receiver(value, &promoted)) {
            return rt_string_ascii_case(promoted, to_lower);
        }
        return rt_core_nil();
    }
    RtCoreString* out = (RtCoreString*)malloc(sizeof(RtCoreString) + (size_t)s->len + 1);
    if (!out) return rt_core_nil();
    out->kind = RT_VALUE_HEAP_STRING;
    out->reserved = 0;
    out->len = s->len;
    for (uint64_t i = 0; i < s->len; i++) {
        char ch = s->data[i];
        if (to_lower && ch >= 'A' && ch <= 'Z') {
            ch = (char)(ch + ('a' - 'A'));
        } else if (!to_lower && ch >= 'a' && ch <= 'z') {
            ch = (char)(ch - ('a' - 'A'));
        }
        out->data[i] = ch;
    }
    out->data[s->len] = '\0';
    if (!rt_core_register_string(out)) {
        free(out);
        return rt_core_nil();
    }
    return (int64_t)(((uint64_t)(uintptr_t)out) | RT_VALUE_TAG_HEAP);
}

int64_t rt_string_to_lower(int64_t value) {
    return rt_string_ascii_case(value, 1);
}

int64_t rt_string_to_upper(int64_t value) {
    return rt_string_ascii_case(value, 0);
}

int64_t rt_string_to_float(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s || s->len == 0) return rt_core_nil();

    char* end = NULL;
    double parsed = strtod(s->data, &end);
    if (end == s->data) return rt_core_nil();

    const char* finish = s->data + s->len;
    while (end < finish &&
           (*end == ' ' || *end == '\t' || *end == '\n' ||
            *end == '\r' || *end == '\f' || *end == '\v')) {
        end++;
    }
    if (end != finish) return rt_core_nil();

    /* rt_value_float takes a double (see its definition above); pass the parsed
     * value directly rather than re-bit-casting it to an i64. */
    return rt_value_float(parsed);
}

int64_t rt_string_split(int64_t value, int64_t delimiter) {
    RtCoreString* s = rt_core_as_string(value);
    RtCoreString* d = rt_core_as_string(delimiter);
    if (!s || !d) return rt_core_nil();
    if (d->len == 0) return rt_string_chars(value);

    uint64_t count = 1;
    for (uint64_t i = 0; i + d->len <= s->len;) {
        if (memcmp(s->data + i, d->data, (size_t)d->len) == 0) {
            count++;
            i += d->len;
        } else {
            i++;
        }
    }

    SplArray* parts = rt_array_new((int64_t)count);
    if (!parts) return rt_core_nil();
    uint64_t start = 0;
    uint64_t i = 0;
    while (i + d->len <= s->len) {
        if (memcmp(s->data + i, d->data, (size_t)d->len) == 0) {
            rt_array_push(parts, rt_string_new((const uint8_t*)s->data + start, i - start));
            i += d->len;
            start = i;
        } else {
            i++;
        }
    }
    rt_array_push(parts, rt_string_new((const uint8_t*)s->data + start, s->len - start));
    return (int64_t)(uintptr_t)parts;
}

int64_t rt_string_split_limit(int64_t value, int64_t delimiter, int64_t limit) {
    RtCoreString* s = rt_core_as_string(value);
    RtCoreString* d = rt_core_as_string(delimiter);
    if (!s || !d) return rt_core_nil();
    if (limit <= 0) return rt_string_split(value, delimiter);
    if (limit == 1) {
        SplArray* one = rt_array_new(1);
        if (!one) return rt_core_nil();
        rt_array_push(one, value);
        return (int64_t)(uintptr_t)one;
    }
    if (d->len == 0) {
        SplArray* parts = rt_array_new(limit);
        if (!parts) return rt_core_nil();
        uint64_t start = 0;
        while (start < s->len && parts->len < limit - 1) {
            rt_array_push(parts, rt_string_new((const uint8_t*)s->data + start, 1));
            start++;
        }
        rt_array_push(parts, rt_string_new((const uint8_t*)s->data + start, s->len - start));
        return (int64_t)(uintptr_t)parts;
    }
    SplArray* parts = rt_array_new(limit);
    if (!parts) return rt_core_nil();
    uint64_t start = 0;
    uint64_t i = 0;
    int64_t count = 1;
    while (i + d->len <= s->len && count < limit) {
        if (memcmp(s->data + i, d->data, (size_t)d->len) == 0) {
            rt_array_push(parts, rt_string_new((const uint8_t*)s->data + start, i - start));
            i += d->len;
            start = i;
            count++;
        } else {
            i++;
        }
    }
    rt_array_push(parts, rt_string_new((const uint8_t*)s->data + start, s->len - start));
    return (int64_t)(uintptr_t)parts;
}

int64_t rt_string_join(int64_t array_value, int64_t separator) {
    RtCoreArray* array = rt_core_as_array(array_value);
    RtCoreString* sep = rt_core_as_string(separator);
    if (!array || !sep) return rt_core_nil();
    uint64_t total = 0;
    for (int64_t i = 0; i < array->len; i++) {
        RtCoreString* item = rt_core_as_string(((int64_t*)array->data)[i]);
        if (item) total += item->len;
        if (i + 1 < array->len) total += sep->len;
    }
    RtCoreString* out = (RtCoreString*)malloc(sizeof(RtCoreString) + (size_t)total + 1);
    if (!out) return rt_core_nil();
    out->kind = RT_VALUE_HEAP_STRING;
    out->reserved = 0;
    out->len = total;
    uint64_t pos = 0;
    for (int64_t i = 0; i < array->len; i++) {
        RtCoreString* item = rt_core_as_string(((int64_t*)array->data)[i]);
        if (item && item->len > 0) {
            memcpy(out->data + pos, item->data, (size_t)item->len);
            pos += item->len;
        }
        if (i + 1 < array->len && sep->len > 0) {
            memcpy(out->data + pos, sep->data, (size_t)sep->len);
            pos += sep->len;
        }
    }
    out->data[total] = '\0';
    if (!rt_core_register_string(out)) {
        free(out);
        return rt_core_nil();
    }
    return (int64_t)(((uint64_t)(uintptr_t)out) | RT_VALUE_TAG_HEAP);
}

/* Join for entry-closure natives (native `[text].join(sep)` lowering):
 * elements pushed at runtime are RAW i64 words — a string literal element is
 * a raw char* GEP, a concat result is a TAGGED handle — so rt_string_join's
 * rt_core_as_string-per-element silently skips raw words (join returned ""
 * and rendered as 0; W100 / "tools":[0]). Normalize each element AND the
 * separator via rt_interp_cstr's tagged-or-raw autodetection instead. */
int64_t rt_array_join_any(int64_t array_value, int64_t separator) {
    RtCoreArray* array = rt_core_as_array(array_value);
    const char* sep = rt_interp_cstr(separator);
    if (!sep) sep = "";
    if (!array) return rt_string_new(NULL, 0);
    size_t sep_len = strlen(sep);
    size_t total = 0;
    for (int64_t i = 0; i < array->len; i++) {
        const char* item = rt_interp_cstr(((int64_t*)array->data)[i]);
        if (item) total += strlen(item);
        if (i + 1 < array->len) total += sep_len;
    }
    RtCoreString* out = (RtCoreString*)malloc(sizeof(RtCoreString) + total + 1);
    if (!out) return rt_string_new(NULL, 0);
    out->kind = RT_VALUE_HEAP_STRING;
    out->reserved = 0;
    out->len = (uint64_t)total;
    size_t pos = 0;
    for (int64_t i = 0; i < array->len; i++) {
        const char* item = rt_interp_cstr(((int64_t*)array->data)[i]);
        if (item) {
            size_t il = strlen(item);
            if (il > 0) { memcpy(out->data + pos, item, il); pos += il; }
        }
        if (i + 1 < array->len && sep_len > 0) {
            memcpy(out->data + pos, sep, sep_len);
            pos += sep_len;
        }
    }
    out->data[total] = '\0';
    if (!rt_core_register_string(out)) {
        free(out);
        return rt_core_nil();
    }
    return (int64_t)(((uint64_t)(uintptr_t)out) | RT_VALUE_TAG_HEAP);
}

int8_t rt_contains(int64_t collection, int64_t value) {
    RtCoreArray* array = rt_core_as_array(collection);
    if (array) {
        for (int64_t i = 0; i < array->len; i++) {
            int64_t item = (array->flags & RT_CORE_ARRAY_FLAG_BYTES)
                ? (int64_t)((uint8_t*)array->data)[i]
                : ((int64_t*)array->data)[i];
            if (rt_native_eq(item, value)) return 1;
        }
        return 0;
    }
    RtCoreDict* dct = rt_core_as_dict(collection);
    if (dct) {
        return (int8_t)rt_core_dict_has(dct, value);
    }
    RtCoreString* s = rt_core_as_string(collection);
    RtCoreString* needle = rt_core_as_string(value);
    if (s && needle) {
        if (needle->len == 0) return 1;
        for (uint64_t i = 0; i + needle->len <= s->len; i++) {
            if (memcmp(s->data + i, needle->data, (size_t)needle->len) == 0) return 1;
        }
        return 0;
    }
    if (s && rt_core_is_int(value)) {
        uint8_t byte = (uint8_t)rt_core_as_int(value);
        for (uint64_t i = 0; i < s->len; i++) {
            if ((uint8_t)s->data[i] == byte) return 1;
        }
    }
    return 0;
}

int64_t rt_unwrap_or_self(int64_t value) {
    /* Only the canonical Option (enum_id 1, Some=0/None=1) unwraps here.
     * `rt_enum_discriminant(value) >= 0` is true for ANY boxed enum, so
     * gating on that alone unwraps user enums to their raw payload instead
     * of returning the enum itself -- see
     * doc/08_tracking/bug/stage3_nil_coalesce_unwraps_user_enum_payload_2026-08-08.md. */
    if (rt_enum_id(value) == 1 && rt_enum_discriminant(value) >= 0) return rt_enum_payload(value);
    return value;
}

/* `.unwrap_or(default)` -- real method-call semantics: return the Ok/Some
 * payload, or `default`, for ANY enum receiver (Result, Option, ...), never
 * trapping. Distinct from `rt_unwrap_or_self` above, which the `??`
 * nil-coalesce operator alone must keep using (only special-cases the
 * reserved Option enum_id 1, returns every other enum -- including Result --
 * unchanged). Routing `.unwrap_or(default)` through `rt_unwrap_or_self`
 * silently returned the boxed `Result` enum for BOTH Ok and Err instead of
 * the payload / the default -- see
 * doc/08_tracking/bug/native_unwrap_returns_enum_wrapper_instead_of_payload_2026-08-11.md.
 * Result has no reserved enum_id, so Ok/Err are identified by
 * discriminant-hash comparison against the canonical variant names, the same
 * technique the Cranelift codegen already uses for is_ok/is_err and the
 * sibling Rust-runtime `rt_unwrap_or_trap`/`rt_unwrap_or_value`. These are
 * `std::collections::hash_map::DefaultHasher` values over the variant name,
 * masked to 32 bits -- fixed/deterministic, precomputed here to avoid
 * reimplementing SipHash in C. */
#define RT_DISC_OK   2405352012u
#define RT_DISC_ERR  4200179024u
#define RT_DISC_SOME 4053299545u
#define RT_DISC_NONE 2371748697u

int64_t rt_unwrap_or_value(int64_t value, int64_t default_val) {
    RtCoreEnum* e = rt_core_as_enum(value);
    if (!e) return value; /* bare/flat-nullable payload convention */

    if (e->enum_id == 1) { /* canonical Option */
        if (e->discriminant == RT_DISC_SOME) return e->payload;
        if (e->discriminant == RT_DISC_NONE) return default_val;
        return value;
    }

    if (e->discriminant == RT_DISC_OK) return e->payload;
    if (e->discriminant == RT_DISC_ERR) return default_val;

    /* Arbitrary user enum: preserve the pre-existing "return self" fallback. */
    return value;
}

int8_t rt_is_none(int64_t value) {
    /* Keep the raw nil sentinel as a migration fallback. Canonical typed
     * Options use enum id 1 with ordinal Some=0 / None=1, so raw zero remains
     * a valid present payload and other enum types are never classified nil. */
    if (value == rt_core_nil()) return 1;
    return rt_enum_id(value) == 1 && rt_enum_discriminant(value) == 1;
}
int8_t rt_is_some(int64_t value) {
    return !rt_is_none(value);
}

/* Repeat a string `count` times.
 *
 * Mirrors the tree-walking interpreter (interpreter_method/string.rs, arm
 * "repeat") and the pure-Simple str_repeat in src/lib/common/string_core.spl:
 * a non-positive count yields the empty string. Kept in step with
 * rt_string_repeat in the Rust runtime (runtime/src/value/collections.rs) --
 * the native lane links THIS file, so a Rust-only definition would leave
 * native `.repeat()` unresolved. */
int64_t rt_string_repeat(int64_t value, int64_t count) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) {
        int64_t promoted;
        if (rt_string_promote_raw_receiver(value, &promoted)) {
            return rt_string_repeat(promoted, count);
        }
        return value;
    }
    if (count <= 0 || s->len == 0) return rt_string_new((const uint8_t*)"", 0);
    if (count == 1) return value;

    uint64_t n = (uint64_t)count;
    if (s->len != 0 && n > (uint64_t)SIZE_MAX / s->len) return rt_core_nil();
    uint64_t out_len = s->len * n;

    RtCoreString* out = (RtCoreString*)malloc(sizeof(RtCoreString) + (size_t)out_len + 1);
    if (!out) return rt_core_nil();
    out->kind = RT_VALUE_HEAP_STRING;
    out->reserved = 0;
    out->len = out_len;
    for (uint64_t i = 0; i < n; i++) {
        memcpy(out->data + i * s->len, s->data, (size_t)s->len);
    }
    out->data[out_len] = '\0';
    if (!rt_core_register_string(out)) {
        free(out);
        return rt_core_nil();
    }
    return (int64_t)(((uint64_t)(uintptr_t)out) | RT_VALUE_TAG_HEAP);
}

/* Character-class predicates: non-empty AND every character in the class.
 *
 * Mirrors interpreter_method/string.rs (arms "is_numeric", "is_alpha",
 * "is_digit", "is_alphanumeric", "is_whitespace") and rt_string_is_* in the
 * Rust runtime (runtime/src/value/collections.rs). The native lane links THIS
 * file, so a Rust-only definition would leave native `.is_digit()` unresolved
 * -- the same way rt_at/rt_array_at were added to the Rust runtime alone and
 * left the native lane broken.
 *
 * KNOWN DIVERGENCE, non-ASCII only: the Rust runtime and the interpreter
 * classify per Unicode `char`, so "e-acute".is_alpha() is true there. This file
 * has no Unicode tables, so any byte >= 0x80 makes the alpha/alnum/whitespace
 * predicates answer 0 rather than guess. is_digit/is_numeric are ASCII-digit by
 * definition, so those two agree with the other engines exactly, everywhere. */
static int64_t rt_string_all_ascii_class(int64_t value, int (*pred)(unsigned char)) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s || s->len == 0) return 0; /* empty string is false for every class */
    for (uint64_t i = 0; i < s->len; i++) {
        unsigned char c = (unsigned char)s->data[i];
        if (c >= 0x80) return 0; /* see KNOWN DIVERGENCE above */
        if (!pred(c)) return 0;
    }
    return 1;
}

static int rt_pred_is_digit(unsigned char c)  { return c >= '0' && c <= '9'; }
static int rt_pred_is_alpha(unsigned char c)  { return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z'); }
static int rt_pred_is_alnum(unsigned char c)  { return rt_pred_is_alpha(c) || rt_pred_is_digit(c); }
static int rt_pred_is_space(unsigned char c)  { return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f' || c == '\v'; }

int64_t rt_string_is_digit(int64_t value)      { return rt_string_all_ascii_class(value, rt_pred_is_digit); }
int64_t rt_string_is_alpha(int64_t value)      { return rt_string_all_ascii_class(value, rt_pred_is_alpha); }
int64_t rt_string_is_alnum(int64_t value)      { return rt_string_all_ascii_class(value, rt_pred_is_alnum); }
int64_t rt_string_is_whitespace(int64_t value) { return rt_string_all_ascii_class(value, rt_pred_is_space); }

/* ---------------------------------------------------------------------------
 * Text methods that had NO runtime definition in EITHER runtime.
 *
 * Each mirrors its arm in the tree-walking interpreter
 * (compiler/src/interpreter_method/string.rs) and the matching rt_string_* in
 * the Rust runtime (runtime/src/value/collections.rs). Before this, the method
 * name fell through every dispatch table to rt_method_not_found.
 *
 * KNOWN DIVERGENCE, non-ASCII only: this file has no Unicode case tables, so
 * capitalize/swapcase/title change case for ASCII letters ONLY and pass every
 * byte >= 0x80 through unchanged, where the Rust runtime and the interpreter
 * apply full Unicode case mapping. Same trade-off, and same reason, as the
 * is_alpha/is_alnum/is_whitespace divergence documented above: guessing a case
 * mapping without tables would be worse than declining one. The remaining
 * functions here (char_count, chomp, trim_*_matches, remove_prefix/suffix,
 * squeeze, replace_first) are codepoint- or byte-exact and agree with the other
 * engines on all input, including non-ASCII.
 * ------------------------------------------------------------------------- */

/* ASCII case/class helpers. Deliberately hand-written rather than <ctype.h>:
 * this file is built for freestanding targets too, and the surrounding
 * rt_pred_is_* predicates already follow this convention. */
static char rt_ascii_upper(unsigned char c) { return (char)((c >= 'a' && c <= 'z') ? c - 32 : c); }
static char rt_ascii_lower(unsigned char c) { return (char)((c >= 'A' && c <= 'Z') ? c + 32 : c); }
/* ASCII punctuation per Rust's char::is_ascii_punctuation: the printable
 * non-alphanumeric, non-space ASCII characters. */
static int rt_ascii_punct(unsigned char c) {
    return (c >= '!' && c <= '/') || (c >= ':' && c <= '@') || (c >= '[' && c <= '`') || (c >= '{' && c <= '~');
}

/* Byte width of the UTF-8 sequence starting at `lead`, clamped to `remaining`.
 * Mirrors the decoder already used by rt_string_chars above. */
static uint64_t rt_utf8_width(const char* data, uint64_t i, uint64_t len) {
    uint8_t lead = (uint8_t)data[i];
    if (lead >= 0xc2 && lead <= 0xdf && i + 2 <= len) return 2;
    if (lead >= 0xe0 && lead <= 0xef && i + 3 <= len) return 3;
    if (lead >= 0xf0 && lead <= 0xf4 && i + 4 <= len) return 4;
    return 1;
}

/* char_count: number of UTF-8 codepoints, as opposed to len (bytes).
 * -1 for a non-text receiver, matching rt_string_len / rt_len. */
int64_t rt_string_char_count(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) return -1;
    int64_t count = 0;
    for (uint64_t i = 0; i < s->len; i += rt_utf8_width(s->data, i, s->len)) count++;
    return count;
}

/* capitalize: uppercase the first character, lowercase the rest (ASCII only). */
int64_t rt_string_capitalize(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) {
        int64_t promoted;
        if (rt_string_promote_raw_receiver(value, &promoted)) {
            return rt_string_capitalize(promoted);
        }
        return value;
    }
    if (s->len == 0) return rt_string_new((const uint8_t*)"", 0);
    char* out = (char*)malloc((size_t)s->len);
    if (!out) return value;
    uint64_t first = rt_utf8_width(s->data, 0, s->len);
    for (uint64_t i = 0; i < s->len; i++) {
        unsigned char c = (unsigned char)s->data[i];
        if (i < first) out[i] = rt_ascii_upper(c);
        else out[i] = rt_ascii_lower(c);
    }
    int64_t result = rt_string_new((const uint8_t*)out, s->len);
    free(out);
    return result;
}

/* swapcase: uppercase <-> lowercase for every character (ASCII only). */
int64_t rt_string_swapcase(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) {
        int64_t promoted;
        if (rt_string_promote_raw_receiver(value, &promoted)) {
            return rt_string_swapcase(promoted);
        }
        return value;
    }
    if (s->len == 0) return rt_string_new((const uint8_t*)"", 0);
    char* out = (char*)malloc((size_t)s->len);
    if (!out) return value;
    for (uint64_t i = 0; i < s->len; i++) {
        unsigned char c = (unsigned char)s->data[i];
        if (c >= 'A' && c <= 'Z') out[i] = rt_ascii_lower(c);
        else if (c >= 'a' && c <= 'z') out[i] = rt_ascii_upper(c);
        else out[i] = (char)c;
    }
    int64_t result = rt_string_new((const uint8_t*)out, s->len);
    free(out);
    return result;
}

/* title / titlecase: uppercase the first character of each word. A word
 * boundary is whitespace OR ASCII punctuation, exactly as the interpreter's
 * arm defines it. */
int64_t rt_string_title(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) {
        int64_t promoted;
        if (rt_string_promote_raw_receiver(value, &promoted)) {
            return rt_string_title(promoted);
        }
        return value;
    }
    if (s->len == 0) return rt_string_new((const uint8_t*)"", 0);
    char* out = (char*)malloc((size_t)s->len);
    if (!out) return value;
    int capitalize_next = 1;
    for (uint64_t i = 0; i < s->len; i++) {
        unsigned char c = (unsigned char)s->data[i];
        if (c < 0x80 && (rt_pred_is_space(c) || rt_ascii_punct(c))) {
            out[i] = (char)c;
            capitalize_next = 1;
        } else if (capitalize_next) {
            out[i] = rt_ascii_upper(c);
            capitalize_next = 0;
        } else {
            out[i] = rt_ascii_lower(c);
        }
    }
    int64_t result = rt_string_new((const uint8_t*)out, s->len);
    free(out);
    return result;
}

/* chomp: strip ONE trailing line terminator -- "\r\n", "\n", or "\r". */
int64_t rt_string_chomp(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) {
        int64_t promoted;
        if (rt_string_promote_raw_receiver(value, &promoted)) {
            return rt_string_chomp(promoted);
        }
        return value;
    }
    uint64_t len = s->len;
    if (len >= 2 && s->data[len - 2] == '\r' && s->data[len - 1] == '\n') len -= 2;
    else if (len >= 1 && (s->data[len - 1] == '\n' || s->data[len - 1] == '\r')) len -= 1;
    if (len == s->len) return value;
    return rt_string_new((const uint8_t*)s->data, len);
}

/* trim_start_matches: repeatedly strip `pattern` from the front. */
int64_t rt_string_trim_start_matches(int64_t value, int64_t pattern) {
    RtCoreString* s = rt_core_as_string(value);
    RtCoreString* p = rt_core_as_string(pattern);
    if (!s || !p) return value;
    if (p->len == 0) return value;
    uint64_t start = 0;
    while (s->len - start >= p->len && memcmp(s->data + start, p->data, (size_t)p->len) == 0) {
        start += p->len;
    }
    if (start == 0) return value;
    return rt_string_new((const uint8_t*)s->data + start, s->len - start);
}

/* trim_end_matches: repeatedly strip `pattern` from the end. */
int64_t rt_string_trim_end_matches(int64_t value, int64_t pattern) {
    RtCoreString* s = rt_core_as_string(value);
    RtCoreString* p = rt_core_as_string(pattern);
    if (!s || !p) return value;
    if (p->len == 0) return value;
    uint64_t end = s->len;
    while (end >= p->len && memcmp(s->data + end - p->len, p->data, (size_t)p->len) == 0) {
        end -= p->len;
    }
    if (end == s->len) return value;
    return rt_string_new((const uint8_t*)s->data, end);
}

/* removeprefix / remove_prefix: strip `prefix` ONCE if present. */
int64_t rt_string_remove_prefix(int64_t value, int64_t prefix) {
    RtCoreString* s = rt_core_as_string(value);
    RtCoreString* p = rt_core_as_string(prefix);
    if (!s || !p) return value;
    if (p->len == 0 || p->len > s->len) return value;
    if (memcmp(s->data, p->data, (size_t)p->len) != 0) return value;
    return rt_string_new((const uint8_t*)s->data + p->len, s->len - p->len);
}

/* removesuffix / remove_suffix: strip `suffix` ONCE if present. */
int64_t rt_string_remove_suffix(int64_t value, int64_t suffix) {
    RtCoreString* s = rt_core_as_string(value);
    RtCoreString* p = rt_core_as_string(suffix);
    if (!s || !p) return value;
    if (p->len == 0 || p->len > s->len) return value;
    if (memcmp(s->data + s->len - p->len, p->data, (size_t)p->len) != 0) return value;
    return rt_string_new((const uint8_t*)s->data, s->len - p->len);
}

/* squeeze: collapse runs of the same adjacent CHARACTER (codepoint, not byte,
 * so "eacute eacute" collapses the same way it does on the other engines).
 *
 * The optional argument restricts the collapse to characters in that set. The
 * dispatch site pads a missing argument with tagged nil, which is not a heap
 * string, so rt_core_as_string yields NULL -- that is the "no argument,
 * squeeze everything" case. An explicit empty string squeezes nothing. */
int64_t rt_string_squeeze(int64_t value, int64_t set) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) {
        int64_t promoted;
        if (rt_string_promote_raw_receiver(value, &promoted)) {
            return rt_string_squeeze(promoted, set);
        }
        return value;
    }
    if (s->len == 0) return rt_string_new((const uint8_t*)"", 0);
    RtCoreString* set_s = rt_core_as_string(set);
    char* out = (char*)malloc((size_t)s->len);
    if (!out) return value;
    uint64_t out_len = 0;
    uint64_t prev_off = 0, prev_w = 0; /* previous character, empty until set */
    for (uint64_t i = 0; i < s->len;) {
        uint64_t w = rt_utf8_width(s->data, i, s->len);
        int squeezable = 1;
        if (set_s) {
            squeezable = 0;
            for (uint64_t j = 0; j + w <= set_s->len; j++) {
                if (memcmp(set_s->data + j, s->data + i, (size_t)w) == 0) { squeezable = 1; break; }
            }
        }
        int same_as_prev = prev_w == w && prev_w != 0 && memcmp(s->data + prev_off, s->data + i, (size_t)w) == 0;
        if (!squeezable || !same_as_prev) {
            memcpy(out + out_len, s->data + i, (size_t)w);
            out_len += w;
        }
        prev_off = i;
        prev_w = w;
        i += w;
    }
    int64_t result = rt_string_new((const uint8_t*)out, out_len);
    free(out);
    return result;
}

/* Codepoint count of a runtime string (helper shared by the pad family). */
static int64_t rt_str_char_count(RtCoreString* s) {
    int64_t n = 0;
    for (uint64_t i = 0; i < s->len; i += rt_utf8_width(s->data, i, s->len)) n++;
    return n;
}

/* First character of the optional pad argument, or ' ' when it was omitted.
 *
 * A missing argument arrives as tagged nil, which is not a heap string, so
 * rt_core_as_string returns NULL. That is unambiguous for a TEXT parameter --
 * unlike an INT parameter, where tagged nil and the integer 3 are the same 64
 * bits. Returns the byte width through *w so a multi-byte pad character pads
 * correctly. */
static const char* rt_pad_char(int64_t pad, uint64_t* w) {
    RtCoreString* p = rt_core_as_string(pad);
    if (!p || p->len == 0) { *w = 1; return " "; }
    *w = rt_utf8_width(p->data, 0, p->len);
    return p->data;
}

/* Shared checked-length arithmetic for string ops that combine a caller- or
 * content-controlled length into an allocation size (pad/zfill/replace_first
 * below; see also rt_string_concat above). An unchecked `a + b` (or `a * b`)
 * can wrap uint64_t, making a tiny malloc succeed while the SUBSEQUENT
 * memcpy/memset calls still use the ORIGINAL un-wrapped operands -- writing
 * past the undersized allocation and silently corrupting adjacent heap
 * memory. Reject loudly via the file's established unrecoverable-error
 * convention (spl_panic) instead of truncating or returning a
 * plausible-looking value. */
static inline uint64_t rt_checked_add_u64(uint64_t a, uint64_t b, const char* ctx) {
    if (a > UINT64_MAX - b) spl_panic(ctx);
    return a + b;
}

static inline uint64_t rt_checked_mul_u64(uint64_t a, uint64_t b, const char* ctx) {
    if (a != 0 && b > UINT64_MAX / a) spl_panic(ctx);
    return a * b;
}

/* pad_left / pad_start: left-pad to `width` CHARACTERS (not bytes).
 * A width at or below the current length is a no-op, so a negative width
 * returns the receiver rather than attempting a huge allocation. */
int64_t rt_string_pad_left(int64_t value, int64_t width, int64_t pad) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) {
        int64_t promoted;
        if (rt_string_promote_raw_receiver(value, &promoted)) {
            return rt_string_pad_left(promoted, width, pad);
        }
        return value;
    }
    int64_t current = rt_str_char_count(s);
    if (width <= current) return value;
    uint64_t pw; const char* pc = rt_pad_char(pad, &pw);
    uint64_t n = (uint64_t)(width - current);
    uint64_t npw = rt_checked_mul_u64(n, pw, "rt_string_pad_left: length overflow");
    uint64_t out_len = rt_checked_add_u64(npw, s->len, "rt_string_pad_left: length overflow");
    char* out = (char*)malloc((size_t)out_len);
    if (!out) return value;
    for (uint64_t i = 0; i < n; i++) memcpy(out + i * pw, pc, (size_t)pw);
    memcpy(out + n * pw, s->data, (size_t)s->len);
    int64_t result = rt_string_new((const uint8_t*)out, out_len);
    free(out);
    return result;
}

/* pad_right / pad_end: right-pad to `width` CHARACTERS. */
int64_t rt_string_pad_right(int64_t value, int64_t width, int64_t pad) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) {
        int64_t promoted;
        if (rt_string_promote_raw_receiver(value, &promoted)) {
            return rt_string_pad_right(promoted, width, pad);
        }
        return value;
    }
    int64_t current = rt_str_char_count(s);
    if (width <= current) return value;
    uint64_t pw; const char* pc = rt_pad_char(pad, &pw);
    uint64_t n = (uint64_t)(width - current);
    uint64_t npw = rt_checked_mul_u64(n, pw, "rt_string_pad_right: length overflow");
    uint64_t out_len = rt_checked_add_u64(s->len, npw, "rt_string_pad_right: length overflow");
    char* out = (char*)malloc((size_t)out_len);
    if (!out) return value;
    memcpy(out, s->data, (size_t)s->len);
    for (uint64_t i = 0; i < n; i++) memcpy(out + s->len + i * pw, pc, (size_t)pw);
    int64_t result = rt_string_new((const uint8_t*)out, out_len);
    free(out);
    return result;
}

/* center: pad both sides to `width` CHARACTERS, extra character on the RIGHT. */
int64_t rt_string_center(int64_t value, int64_t width, int64_t pad) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) {
        int64_t promoted;
        if (rt_string_promote_raw_receiver(value, &promoted)) {
            return rt_string_center(promoted, width, pad);
        }
        return value;
    }
    int64_t current = rt_str_char_count(s);
    if (width <= current) return value;
    uint64_t pw; const char* pc = rt_pad_char(pad, &pw);
    uint64_t total = (uint64_t)(width - current);
    uint64_t left = total / 2;
    uint64_t right = total - left;
    uint64_t lr_pw = rt_checked_mul_u64(rt_checked_add_u64(left, right, "rt_string_center: length overflow"),
                                         pw, "rt_string_center: length overflow");
    uint64_t out_len = rt_checked_add_u64(lr_pw, s->len, "rt_string_center: length overflow");
    char* out = (char*)malloc((size_t)out_len);
    if (!out) return value;
    uint64_t o = 0;
    for (uint64_t i = 0; i < left; i++, o += pw) memcpy(out + o, pc, (size_t)pw);
    memcpy(out + o, s->data, (size_t)s->len); o += s->len;
    for (uint64_t i = 0; i < right; i++, o += pw) memcpy(out + o, pc, (size_t)pw);
    int64_t result = rt_string_new((const uint8_t*)out, out_len);
    free(out);
    return result;
}

/* zfill: left-pad with '0' to `width` CHARACTERS, keeping a leading sign in
 * front of the zeros ("-7".zfill(4) is "-007", not "00-7"). */
int64_t rt_string_zfill(int64_t value, int64_t width) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) {
        int64_t promoted;
        if (rt_string_promote_raw_receiver(value, &promoted)) {
            return rt_string_zfill(promoted, width);
        }
        return value;
    }
    int64_t current = rt_str_char_count(s);
    if (width <= current) return value;
    uint64_t sign = (s->len > 0 && (s->data[0] == '+' || s->data[0] == '-')) ? 1 : 0;
    uint64_t zeros = (uint64_t)(width - current);
    uint64_t out_len = rt_checked_add_u64(s->len, zeros, "rt_string_zfill: length overflow");
    char* out = (char*)malloc((size_t)out_len);
    if (!out) return value;
    if (sign) out[0] = s->data[0];
    memset(out + sign, '0', (size_t)zeros);
    memcpy(out + sign + zeros, s->data + sign, (size_t)(s->len - sign));
    int64_t result = rt_string_new((const uint8_t*)out, out_len);
    free(out);
    return result;
}

/* find_all / find_indices: BYTE offsets of every non-overlapping match.
 * An empty needle yields an EMPTY array, matching the interpreter's guard. */
int64_t rt_string_find_all(int64_t value, int64_t needle) {
    RtCoreString* s = rt_core_as_string(value);
    RtCoreString* n = rt_core_as_string(needle);
    SplArray* out = rt_array_new(0);
    if (!out) return rt_core_nil();
    if (!s || !n || n->len == 0) return (int64_t)(uintptr_t)out;
    for (uint64_t i = 0; i + n->len <= s->len;) {
        if (memcmp(s->data + i, n->data, (size_t)n->len) == 0) {
            rt_array_push(out, rt_value_int((int64_t)i));
            i += n->len;
        } else {
            i++;
        }
    }
    return (int64_t)(uintptr_t)out;
}

/* substr(start, length): CHARACTER-indexed substring by start and length.
 * Deliberately NOT rt_slice, which is byte-indexed. Negative arguments clamp
 * to 0, matching the saturating eval_arg_usize in the interpreter. */
int64_t rt_string_substr(int64_t value, int64_t start, int64_t length) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) {
        int64_t promoted;
        if (rt_string_promote_raw_receiver(value, &promoted)) {
            return rt_string_substr(promoted, start, length);
        }
        return value;
    }
    if (start < 0) start = 0;
    if (length < 0) length = 0;
    uint64_t b = 0;
    int64_t skipped = 0;
    while (b < s->len && skipped < start) { b += rt_utf8_width(s->data, b, s->len); skipped++; }
    uint64_t e = b;
    int64_t taken = 0;
    while (e < s->len && taken < length) { e += rt_utf8_width(s->data, e, s->len); taken++; }
    return rt_string_new((const uint8_t*)s->data + b, e - b);
}

/* substr(start): CHARACTER-indexed substring from `start` to the end.
 * A separate symbol rather than a default argument, because the omitted-slot
 * padding value (tagged nil) IS the integer 3 for an int parameter. */
int64_t rt_string_substr_from(int64_t value, int64_t start) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) {
        int64_t promoted;
        if (rt_string_promote_raw_receiver(value, &promoted)) {
            return rt_string_substr_from(promoted, start);
        }
        return value;
    }
    if (start < 0) start = 0;
    uint64_t b = 0;
    int64_t skipped = 0;
    while (b < s->len && skipped < start) { b += rt_utf8_width(s->data, b, s->len); skipped++; }
    return rt_string_new((const uint8_t*)s->data + b, s->len - b);
}

/* Refuse a non-text receiver LOUDLY.
 *
 * The dispatch tables are keyed on the method NAME only, with no receiver type,
 * so a name shared with an array method reaches the text entry point with the
 * wrong receiver. Returning a plausible-looking value there is how this whole
 * bug started. These names had no compiled implementation at all before, so
 * exiting is exactly as loud as the behaviour it replaces, never quieter. */
static void rt_refuse_non_text_receiver(const char* method, int64_t receiver) {
    fprintf(stderr,
            "Runtime error: str.%s was called on a receiver that is not text. "
            "This method has no compiled implementation for that receiver type -- "
            "a code-generation dispatch gap, not a program error. Refusing to "
            "substitute a value. receiver=0x%llx\n",
            method, (unsigned long long)receiver);
    exit(70);
}

/* Reverse the CHARACTERS of a runtime string (helper, no receiver check). */
static int64_t rt_string_reverse_chars(RtCoreString* s) {
    if (s->len == 0) return rt_string_new((const uint8_t*)"", 0);
    char* out = (char*)malloc((size_t)s->len);
    if (!out) return rt_core_nil();
    uint64_t o = s->len;
    for (uint64_t i = 0; i < s->len;) {
        uint64_t w = rt_utf8_width(s->data, i, s->len);
        o -= w;
        memcpy(out + o, s->data + i, (size_t)w);
        i += w;
    }
    int64_t result = rt_string_new((const uint8_t*)out, s->len);
    free(out);
    return result;
}

/* rev / reversed: reverse by CHARACTER for text, by ELEMENT for an array.
 * Receiver-dispatched, following the rt_at/rt_array_at precedent.
 *
 * `reverse` now routes here too, on every type-blind dispatch table. It used to
 * point at rt_array_reverse, which this file has never defined, so
 * `arr.reverse()` was an unresolved symbol on the native lane; on the Rust lane
 * it resolved to an IN-PLACE reverse returning a bool, for every receiver
 * including text. The interpreter is the spec and mutates nothing --
 * interpreter_method/collections.rs "rev" | "reverse" copies then reverses, and
 * the string arm builds a new text -- which is exactly what this function
 * does. */
int64_t rt_reverse(int64_t receiver) {
    /* rt_core_as_array validates the header; SplArray* carries the tagged
     * value directly, exactly as rt_array_len_safe does. */
    SplArray* arr = rt_core_as_array(receiver) ? (SplArray*)(uintptr_t)receiver : NULL;
    if (arr) {
        int64_t n = rt_array_len(arr);
        SplArray* out = rt_array_new(n > 0 ? n : 0);
        if (!out) return rt_core_nil();
        for (int64_t i = n - 1; i >= 0; i--) rt_array_push(out, rt_array_get(arr, i));
        return (int64_t)(uintptr_t)out;
    }
    RtCoreString* s = rt_core_as_string(receiver);
    if (!s) rt_refuse_non_text_receiver("rev", receiver);
    return rt_string_reverse_chars(s);
}

/* reverse: the MUTATING spelling. Reverses an ARRAY in place and returns that
 * same array.
 *
 * `reverse` and `rev`/`reversed` are NOT synonyms here. interpreter_method/mod.c
 * -- interpreter_method/mod.rs -- lists "reverse" in MUTATING_METHODS and
 * deliberately does NOT list "rev"/"reversed", so the interpreter writes the
 * result back to the receiver binding for `reverse` only. Both spellings share
 * ONE arm in interpreter_method/collections.rs, which is exactly why reading
 * that arm alone makes them look identical. Measured:
 *
 *   var a = [1, 2, 3]
 *   a.reverse()   -> [3,2,1] AND a == [3,2,1]   (mutating spelling)
 *   a.rev()       -> [3,2,1] AND a == [1,2,3]   (pure spelling)
 *
 * Routing `reverse` to the copying rt_reverse left the receiver unmodified on
 * JIT/native while the interpreter rebound it -- a silent wrong answer on the
 * aliasing axis. rt_reverse itself is CORRECT: it is the rev/reversed helper.
 *
 * TEXT passes through to the copying behaviour UNCHANGED. The interpreter also
 * rebinds a text receiver, contradicting its own documented rule that strings
 * are value types with no mutating methods; that affects string push/pop/clear
 * too and is recorded in the bug tracker rather than decided here. */
int64_t rt_reverse_mut(int64_t receiver) {
    SplArray* arr = rt_core_as_array(receiver) ? (SplArray*)(uintptr_t)receiver : NULL;
    if (arr) {
        int64_t n = rt_array_len(arr);
        for (int64_t i = 0, j = n - 1; i < j; i++, j--) {
            int64_t tmp = rt_array_get(arr, i);
            rt_array_set(arr, i, rt_array_get(arr, j));
            rt_array_set(arr, j, tmp);
        }
        return receiver;
    }
    RtCoreString* s = rt_core_as_string(receiver);
    if (!s) rt_refuse_non_text_receiver("reverse", receiver);
    return rt_string_reverse_chars(s);
}

/* A receiver `sort` has no compiled implementation for. Loud, never a value.
 * Separate from rt_refuse_non_text_receiver because `sort` is the opposite
 * shape: text is the INVALID receiver here, not the valid one. */
static void rt_refuse_non_array_sort_receiver(void) {
    fprintf(stderr,
            "Runtime error: sort() was called on a receiver that is not an array. "
            "The interpreter refuses this outright (\"method `sort` not found on "
            "type `str`\"), so there is no correct value to return. Refusing to "
            "substitute one.\n");
    exit(70);
}

/* Ordering for `sort`, pinned to the interpreter's comparator.
 *
 * interpreter_method/collections.rs "sort" is the spec:
 *   (Int, Int)     => a.cmp(b)
 *   (Float, Float) => a.partial_cmp(b) or Equal
 *   (Str, Str)     => a.cmp(b)
 *   _              => Equal
 *
 * MIXED types compare Equal and the sort is STABLE, so a mixed array keeps its
 * original relative order. */
static int rt_sort_cmp(int64_t a, int64_t b) {
    if (rt_core_is_int(a) && rt_core_is_int(b)) {
        int64_t x = rt_core_as_int(a), y = rt_core_as_int(b);
        return x < y ? -1 : (x > y ? 1 : 0);
    }
    if (rt_core_is_float(a) && rt_core_is_float(b)) {
        double x = rt_core_as_float(a), y = rt_core_as_float(b);
        if (x < y) return -1;
        if (x > y) return 1;
        return 0; /* equal, or a NaN pair -> Equal, matching unwrap_or(Equal) */
    }
    RtCoreString* sa = rt_core_as_string(a);
    RtCoreString* sb = rt_core_as_string(b);
    if (sa && sb) {
        uint64_t n = sa->len < sb->len ? sa->len : sb->len;
        int c = n ? memcmp(sa->data, sb->data, (size_t)n) : 0;
        if (c != 0) return c < 0 ? -1 : 1;
        if (sa->len == sb->len) return 0;
        return sa->len < sb->len ? -1 : 1;
    }
    return 0;
}

/* sort: sort an ARRAY in place and return that same array.
 *
 * `sort` used to point at rt_array_sort on every type-blind dispatch table.
 * This file has never defined that symbol, so arr.sort() was an unresolved
 * symbol on the native lane; on the Rust lane it resolved to an in-place sort
 * returning a BOOL, for every receiver including text, and the value only came
 * out right because codegen substituted the receiver vreg via its in_place set
 * -- which also silently handed back an unsorted TEXT receiver.
 *
 * The interpreter is the spec, and reading interpreter_method/collections.rs
 * alone gets it WRONG: that arm copies, but interpreter_method/mod.rs then
 * writes the result back to the receiver binding because "sort" is in its
 * MUTATING_METHODS list. Measured end to end on the interpreter:
 *
 *   var a = [3, 1, 2]
 *   val b = a.sort()     // b = [1, 2, 3]  AND  a = [1, 2, 3]
 *   "cba".sort()         // error: method `sort` not found on type `str` (rc=1)
 *
 * So: sort in place, return the receiver, refuse anything that is not an array.
 *
 * Insertion sort, because it is STABLE (matching Rust's sort_by) and the
 * comparator is a plain function; array sizes here are the same ones the rest
 * of this file already handles element-at-a-time. */
int64_t rt_sort(int64_t receiver) {
    SplArray* arr = rt_core_as_array(receiver) ? (SplArray*)(uintptr_t)receiver : NULL;
    if (!arr) rt_refuse_non_array_sort_receiver();
    int64_t n = rt_array_len(arr);
    if (n < 0) n = 0;
    if (n < 2) return receiver;
    int64_t* buf = (int64_t*)malloc((size_t)n * sizeof(int64_t));
    if (!buf) return receiver;
    for (int64_t i = 0; i < n; i++) buf[i] = rt_array_get(arr, i);
    for (int64_t i = 1; i < n; i++) {
        int64_t key = buf[i];
        int64_t j = i - 1;
        /* strict `> 0` keeps equal elements in original order = stable */
        while (j >= 0 && rt_sort_cmp(buf[j], key) > 0) {
            buf[j + 1] = buf[j];
            j--;
        }
        buf[j + 1] = key;
    }
    for (int64_t i = 0; i < n; i++) rt_array_set(arr, i, buf[i]);
    free(buf);
    return receiver;
}

/* take / taken: first n CHARACTERS of text, or first n ELEMENTS of an array.
 * A negative n yields an empty result, matching the saturating eval_arg_usize. */
int64_t rt_take(int64_t receiver, int64_t n) {
    if (n < 0) n = 0;
    /* rt_core_as_array validates the header; SplArray* carries the tagged
     * value directly, exactly as rt_array_len_safe does. */
    SplArray* arr = rt_core_as_array(receiver) ? (SplArray*)(uintptr_t)receiver : NULL;
    if (arr) {
        int64_t len = rt_array_len(arr);
        int64_t take = n < len ? n : len;
        SplArray* out = rt_array_new(take > 0 ? take : 0);
        if (!out) return rt_core_nil();
        for (int64_t i = 0; i < take; i++) rt_array_push(out, rt_array_get(arr, i));
        return (int64_t)(uintptr_t)out;
    }
    RtCoreString* s = rt_core_as_string(receiver);
    if (!s) rt_refuse_non_text_receiver("take", receiver);
    uint64_t e = 0;
    int64_t taken = 0;
    while (e < s->len && taken < n) { e += rt_utf8_width(s->data, e, s->len); taken++; }
    return rt_string_new((const uint8_t*)s->data, e);
}

/* drop / dropped / skip: all but the first n CHARACTERS / ELEMENTS. */
int64_t rt_drop(int64_t receiver, int64_t n) {
    if (n < 0) n = 0;
    /* rt_core_as_array validates the header; SplArray* carries the tagged
     * value directly, exactly as rt_array_len_safe does. */
    SplArray* arr = rt_core_as_array(receiver) ? (SplArray*)(uintptr_t)receiver : NULL;
    if (arr) {
        int64_t len = rt_array_len(arr);
        int64_t start = n < len ? n : len;
        SplArray* out = rt_array_new(len - start > 0 ? len - start : 0);
        if (!out) return rt_core_nil();
        for (int64_t i = start; i < len; i++) rt_array_push(out, rt_array_get(arr, i));
        return (int64_t)(uintptr_t)out;
    }
    RtCoreString* s = rt_core_as_string(receiver);
    if (!s) rt_refuse_non_text_receiver("drop", receiver);
    uint64_t b = 0;
    int64_t skipped = 0;
    while (b < s->len && skipped < n) { b += rt_utf8_width(s->data, b, s->len); skipped++; }
    return rt_string_new((const uint8_t*)s->data + b, s->len - b);
}

/* sorted on TEXT: the receiver's characters in codepoint order.
 *
 * TEXT ONLY, on purpose, in BOTH runtimes. Ordering an array means ordering
 * tag-boxed values of mixed type, and this file has no such comparator (nor an
 * rt_array_sorted). Implementing it in the Rust runtime alone would make the
 * lanes disagree on arr.sorted(); declining loudly keeps them identical and
 * leaves array `sorted` exactly as unwired as it already is. */
int64_t rt_string_sorted(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) rt_refuse_non_text_receiver("sorted", value);
    if (s->len == 0) return rt_string_new((const uint8_t*)"", 0);
    /* Collect codepoint spans, insertion-sort them by codepoint value, emit. */
    uint64_t n = 0;
    for (uint64_t i = 0; i < s->len; i += rt_utf8_width(s->data, i, s->len)) n++;
    uint64_t* off = (uint64_t*)malloc((size_t)n * sizeof(uint64_t));
    uint64_t* wid = (uint64_t*)malloc((size_t)n * sizeof(uint64_t));
    uint32_t* cp  = (uint32_t*)malloc((size_t)n * sizeof(uint32_t));
    if (!off || !wid || !cp) { free(off); free(wid); free(cp); return value; }
    uint64_t k = 0;
    for (uint64_t i = 0; i < s->len;) {
        uint64_t w = rt_utf8_width(s->data, i, s->len);
        uint32_t c;
        unsigned char lead = (unsigned char)s->data[i];
        if (w == 1) c = lead;
        else if (w == 2) c = ((uint32_t)(lead & 0x1F) << 6) | ((unsigned char)s->data[i+1] & 0x3F);
        else if (w == 3) c = ((uint32_t)(lead & 0x0F) << 12) | (((unsigned char)s->data[i+1] & 0x3F) << 6)
                             | ((unsigned char)s->data[i+2] & 0x3F);
        else c = ((uint32_t)(lead & 0x07) << 18) | (((unsigned char)s->data[i+1] & 0x3F) << 12)
                 | (((unsigned char)s->data[i+2] & 0x3F) << 6) | ((unsigned char)s->data[i+3] & 0x3F);
        off[k] = i; wid[k] = w; cp[k] = c; k++;
        i += w;
    }
    for (uint64_t i = 1; i < n; i++) {
        uint64_t o = off[i], w = wid[i]; uint32_t c = cp[i];
        int64_t j = (int64_t)i - 1;
        while (j >= 0 && cp[j] > c) { off[j+1] = off[j]; wid[j+1] = wid[j]; cp[j+1] = cp[j]; j--; }
        off[j+1] = o; wid[j+1] = w; cp[j+1] = c;
    }
    char* out = (char*)malloc((size_t)s->len);
    if (!out) { free(off); free(wid); free(cp); return value; }
    uint64_t o = 0;
    for (uint64_t i = 0; i < n; i++) { memcpy(out + o, s->data + off[i], (size_t)wid[i]); o += wid[i]; }
    int64_t result = rt_string_new((const uint8_t*)out, o);
    free(out); free(off); free(wid); free(cp);
    return result;
}

/* Shared body for partition / rpartition: [before, separator, after].
 * An empty or absent separator puts the receiver in the FIRST slot for
 * partition and the LAST slot for rpartition, matching the interpreter arms. */
static int64_t rt_string_partition_at(int64_t value, int64_t sep_value, int from_end, const char* who) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) rt_refuse_non_text_receiver(who, value);
    RtCoreString* sep = rt_core_as_string(sep_value);
    SplArray* out = rt_array_new(3);
    if (!out) return rt_core_nil();
    int64_t hit = -1;
    if (sep && sep->len > 0 && sep->len <= s->len) {
        if (from_end) {
            for (int64_t i = (int64_t)(s->len - sep->len); i >= 0; i--) {
                if (memcmp(s->data + i, sep->data, (size_t)sep->len) == 0) { hit = i; break; }
            }
        } else {
            for (uint64_t i = 0; i + sep->len <= s->len; i++) {
                if (memcmp(s->data + i, sep->data, (size_t)sep->len) == 0) { hit = (int64_t)i; break; }
            }
        }
    }
    if (hit >= 0) {
        rt_array_push(out, rt_string_new((const uint8_t*)s->data, (uint64_t)hit));
        rt_array_push(out, rt_string_new((const uint8_t*)sep->data, sep->len));
        rt_array_push(out, rt_string_new((const uint8_t*)s->data + hit + sep->len,
                                         s->len - (uint64_t)hit - sep->len));
    } else if (from_end) {
        rt_array_push(out, rt_string_new((const uint8_t*)"", 0));
        rt_array_push(out, rt_string_new((const uint8_t*)"", 0));
        rt_array_push(out, rt_string_new((const uint8_t*)s->data, s->len));
    } else {
        rt_array_push(out, rt_string_new((const uint8_t*)s->data, s->len));
        rt_array_push(out, rt_string_new((const uint8_t*)"", 0));
        rt_array_push(out, rt_string_new((const uint8_t*)"", 0));
    }
    return (int64_t)(uintptr_t)out;
}

/* partition: split at the FIRST occurrence. TEXT ONLY -- the array `partition`
 * takes a PREDICATE and returns [passing, failing], a different arity, argument
 * type and result shape, and invoking a closure is not possible from here. */
int64_t rt_string_partition(int64_t value, int64_t sep) {
    return rt_string_partition_at(value, sep, 0, "partition");
}

/* rpartition: split at the LAST occurrence. */
int64_t rt_string_rpartition(int64_t value, int64_t sep) {
    return rt_string_partition_at(value, sep, 1, "rpartition");
}

/* replace_first: replace only the FIRST occurrence of `pattern`. */
int64_t rt_string_replace_first(int64_t value, int64_t pattern, int64_t replacement) {
    RtCoreString* s = rt_core_as_string(value);
    RtCoreString* p = rt_core_as_string(pattern);
    RtCoreString* r = rt_core_as_string(replacement);
    if (!s || !p || !r) return value;
    if (p->len > s->len) return value;
    /* An empty pattern matches at offset 0, so replace_first("", x) prepends x
     * -- what Rust's str::replacen does, and therefore what the interpreter
     * arm does. */
    for (uint64_t i = 0; i + p->len <= s->len; i++) {
        if (memcmp(s->data + i, p->data, (size_t)p->len) != 0) continue;
        uint64_t out_len = rt_checked_add_u64(s->len - p->len, r->len,
                                               "rt_string_replace_first: length overflow");
        char* out = (char*)malloc((size_t)out_len > 0 ? (size_t)out_len : 1);
        if (!out) return value;
        memcpy(out, s->data, (size_t)i);
        memcpy(out + i, r->data, (size_t)r->len);
        memcpy(out + i + r->len, s->data + i + p->len, (size_t)(s->len - i - p->len));
        int64_t result = rt_string_new((const uint8_t*)out, out_len);
        free(out);
        return result;
    }
    return value;
}

int64_t rt_string_replace(int64_t value, int64_t old_value, int64_t new_value) {
    RtCoreString* s = rt_core_as_string(value);
    RtCoreString* old_s = rt_core_as_string(old_value);
    RtCoreString* new_s = rt_core_as_string(new_value);
    if (!s || !old_s || !new_s) return value;
    if (old_s->len == 0) return value;

    uint64_t count = 0;
    for (uint64_t i = 0; old_s->len <= s->len - i;) {
        if (memcmp(s->data + i, old_s->data, (size_t)old_s->len) == 0) {
            count++;
            i += old_s->len;
        } else {
            i++;
        }
    }
    if (count == 0) return value;
    uint64_t out_len = s->len;
    if (new_s->len >= old_s->len) {
        out_len += count * (new_s->len - old_s->len);
    } else {
        out_len -= count * (old_s->len - new_s->len);
    }
    RtCoreString* out = (RtCoreString*)malloc(sizeof(RtCoreString) + (size_t)out_len + 1);
    if (!out) return rt_core_nil();
    out->kind = RT_VALUE_HEAP_STRING;
    out->reserved = 0;
    out->len = out_len;
    uint64_t in_i = 0;
    uint64_t out_i = 0;
    while (in_i < s->len) {
        if (old_s->len <= s->len - in_i && memcmp(s->data + in_i, old_s->data, (size_t)old_s->len) == 0) {
            if (new_s->len > 0) memcpy(out->data + out_i, new_s->data, (size_t)new_s->len);
            out_i += new_s->len;
            in_i += old_s->len;
        } else {
            out->data[out_i++] = s->data[in_i++];
        }
    }
    out->data[out_len] = '\0';
    if (!rt_core_register_string(out)) {
        free(out);
        return rt_core_nil();
    }
    return (int64_t)(((uint64_t)(uintptr_t)out) | RT_VALUE_TAG_HEAP);
}

/* A raw, unregistered `char*` receiver does not decode via rt_core_as_string.
 * Promote a plausible raw pointer to a real heap string so the callers below
 * can recurse once into their already-correct heap-string path. Same
 * conservative floor as rt_interp_cstr: < 0x10000 is nil/bool/small-int and is
 * never dereferenced. */
static int rt_string_promote_raw_receiver(int64_t value, int64_t* out) {
    if (value < 0x10000) return 0;
    const char* p = (const char*)(uintptr_t)value;
    *out = rt_string_new((const uint8_t*)p, (uint64_t)strlen(p));
    return 1;
}

int64_t rt_string_trim(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) {
        int64_t promoted;
        if (rt_string_promote_raw_receiver(value, &promoted)) return rt_string_trim(promoted);
        return value;
    }
    uint64_t begin = 0;
    uint64_t end = s->len;
    while (begin < end && (s->data[begin] == ' ' || s->data[begin] == '\t' || s->data[begin] == '\n' || s->data[begin] == '\r')) {
        begin++;
    }
    while (end > begin && (s->data[end - 1] == ' ' || s->data[end - 1] == '\t' || s->data[end - 1] == '\n' || s->data[end - 1] == '\r')) {
        end--;
    }
    return rt_string_new((const uint8_t*)s->data + begin, end - begin);
}

int64_t rt_string_trim_start(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) {
        int64_t promoted;
        if (rt_string_promote_raw_receiver(value, &promoted)) return rt_string_trim_start(promoted);
        return value;
    }
    uint64_t begin = 0;
    while (begin < s->len && (s->data[begin] == ' ' || s->data[begin] == '\t' ||
                              s->data[begin] == '\n' || s->data[begin] == '\v' ||
                              s->data[begin] == '\f' || s->data[begin] == '\r')) {
        begin++;
    }
    return rt_string_new((const uint8_t*)s->data + begin, s->len - begin);
}

int64_t rt_string_trim_end(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) {
        int64_t promoted;
        if (rt_string_promote_raw_receiver(value, &promoted)) return rt_string_trim_end(promoted);
        return value;
    }
    uint64_t end = s->len;
    while (end > 0 && (s->data[end - 1] == ' ' || s->data[end - 1] == '\t' ||
                       s->data[end - 1] == '\n' || s->data[end - 1] == '\r')) {
        end--;
    }
    return rt_string_new((const uint8_t*)s->data, end);
}

int64_t rt_string_to_int(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) return 0;
    char buf[64];
    uint64_t n = s->len < sizeof(buf) - 1 ? s->len : sizeof(buf) - 1;
    if (n > 0) memcpy(buf, s->data, (size_t)n);
    buf[n] = '\0';
    return (int64_t)strtoll(buf, NULL, 10);
}

/* Task #178 (text3 lane): backs the `int("42")` global builtin's native MIR
 * lowering (switch_operators_calls.spl). rt_string_to_int above requires an
 * ALREADY-tagged receiver (rt_core_as_string-checked, 0 otherwise) -- the
 * same trap that previously silently broke `.len()`/`.substring()` on a
 * genuinely-raw string literal argument (e.g. `int("42")`'s "42" is a bare
 * literal, never wrapped by rt_string_new). Normalize via rt_interp_cstr
 * first (the same tagged-or-raw runtime autodetection used throughout this
 * file, bug #136) to get a definite raw buffer regardless of the argument's
 * actual representation, then strtoll it directly -- safe for both a tagged
 * runtime string and a raw char* literal, and does not change
 * rt_string_to_int's own behavior for its existing to_i64()/parse_int()/
 * to_int() callers. */
int64_t rt_string_to_int_any(int64_t value) {
    const char* raw = rt_interp_cstr(value);
    if (!raw) return 0;
    return (int64_t)strtoll(raw, NULL, 10);
}

/* Task #118: sibling of rt_string_to_int() with the canonical `int(text)`
 * semantics — a total, leading-numeric-prefix parse (strtoll already IS
 * this: it skips whitespace/sign, parses leading digits, stops at the first
 * non-digit, returns 0 if none). Named distinctly from rt_string_to_int so
 * the Rust-native `simple-runtime` crate's stricter, whole-string-match
 * rt_string_to_int() (used by .to_int()/.parse_int()/to_i64()) is
 * unaffected; the two are byte-for-byte identical here because this C
 * runtime's rt_string_to_int() already implements the lenient behavior. */
int64_t rt_string_to_int_lenient(int64_t value) {
    return rt_string_to_int(value);
}

void rt_print_str(const uint8_t* ptr, uint64_t len) {
    rt_core_write_bytes(stdout, ptr, len);
    fflush(stdout);
}

void rt_println_str(const uint8_t* ptr, uint64_t len) {
    rt_print_str(ptr, len);
    fputc('\n', stdout);
    fflush(stdout);
}

void rt_eprint_str(const uint8_t* ptr, uint64_t len) {
    rt_core_write_bytes(stderr, ptr, len);
    fflush(stderr);
}

void rt_eprintln_str(const uint8_t* ptr, uint64_t len) {
    rt_eprint_str(ptr, len);
    fputc('\n', stderr);
    fflush(stderr);
}

void rt_print_value(int64_t value) {
    rt_core_print_value_to(stdout, value);
    fflush(stdout);
}

void rt_println_value(int64_t value) {
    rt_core_print_value_to(stdout, value);
    fputc('\n', stdout);
    fflush(stdout);
}

void serial_println(int64_t value) {
    rt_println_value(value);
}

void rt_eprint_value(int64_t value) {
    rt_core_print_value_to(stderr, value);
    fflush(stderr);
}

void rt_eprintln_value(int64_t value) {
    rt_core_print_value_to(stderr, value);
    fputc('\n', stderr);
    fflush(stderr);
}

static int rt_core_argc = 0;
static char** rt_core_argv = NULL;

__attribute__((weak)) void spl_init_args(int argc, char** argv) {
    rt_core_argc = argc;
    rt_core_argv = argv;
}

__attribute__((weak)) int64_t spl_arg_count(void) {
    return (int64_t)rt_core_argc;
}

__attribute__((weak)) const char* spl_get_arg(int64_t idx) {
    if (idx < 0 || idx >= rt_core_argc) return "";
    return rt_core_argv && rt_core_argv[idx] ? rt_core_argv[idx] : "";
}

__attribute__((weak)) void rt_set_args(int argc, char** argv) {
    spl_init_args(argc, argv);
}

__attribute__((weak)) int32_t rt_get_argc(void) {
    return (int32_t)spl_arg_count();
}

__attribute__((weak)) SplArray* rt_get_args(void) {
    return rt_cli_get_args();
}

/* sys_get_args: the extern name std.io_runtime declares for argv (the seed
 * interpreter registers it on every lane). No native C definition existed, so
 * entry-closure binaries linked it as a silent 0-returning stub and
 * get_args() saw an empty array (native_sys_get_args_missing 2026-07-23). */
__attribute__((weak)) SplArray* sys_get_args(void) {
    return rt_cli_get_args();
}

__attribute__((weak)) SplArray* rt_cli_get_args(void) {
    int64_t argc = spl_arg_count();
    SplArray* args = rt_array_new(argc);
    if (!args) return (SplArray*)rt_core_nil();
    for (int64_t i = 0; i < argc; i++) {
        const char* arg = spl_get_arg(i);
        int64_t value = rt_string_new((const uint8_t*)arg, (uint64_t)strlen(arg));
        rt_array_push(args, value);
    }
    return args;
}

__attribute__((weak)) int64_t rt_cli_arg_count(void) {
    return spl_arg_count();
}

__attribute__((weak)) int64_t rt_cli_arg_at(int64_t index) {
    if (index < 0 || index >= spl_arg_count()) {
        return rt_string_new(NULL, 0);
    }
    const char* arg = spl_get_arg(index);
    if (!arg) arg = "";
    return rt_string_new((const uint8_t*)arg, (uint64_t)strlen(arg));
}

int64_t rt_file_preload_pages(int64_t path_value) {
#if defined(_WIN32)
    (void)path_value;
    return -1;
#else
    RtCoreString* path = rt_core_as_string(path_value);
    if (!path) return -1;
    char* cpath = (char*)malloc((size_t)path->len + 1);
    if (!cpath) return -1;
    memcpy(cpath, path->data, (size_t)path->len);
    cpath[path->len] = '\0';

    int fd = open(cpath, O_RDONLY);
    free(cpath);
    if (fd < 0) return -2;

    off_t size = lseek(fd, 0, SEEK_END);
    if (size <= 0) {
        close(fd);
        return 0;
    }
    lseek(fd, 0, SEEK_SET);

    unsigned char* mapped = (unsigned char*)mmap(NULL, (size_t)size, PROT_READ, MAP_PRIVATE, fd, 0);
    close(fd);
    if (mapped == MAP_FAILED) return -3;

    volatile uint64_t sum = 0;
    int64_t pages = 0;
    for (off_t pos = 0; pos < size; pos += 4096) {
        sum += mapped[pos];
        pages++;
    }
    munmap(mapped, (size_t)size);
    return pages + (int64_t)(sum & 0);
#endif
}

#if !defined(_WIN32)
static int rt_core_sockaddr_loopback(uint16_t port, struct sockaddr_in* out) {
    if (!out) return -1;
    memset(out, 0, sizeof(*out));
    out->sin_family = AF_INET;
    out->sin_port = htons(port);
    out->sin_addr.s_addr = htonl(0x7f000001u);
    return 0;
}
#endif

int64_t rt_net_tcp_connect_local_discard(void) {
#if defined(_WIN32)
    return -1;
#else
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return -1;
    struct sockaddr_in addr;
    rt_core_sockaddr_loopback(9, &addr);
    connect(fd, (struct sockaddr*)&addr, sizeof(addr));
    close(fd);
    return 0;
#endif
}

int64_t rt_net_udp_send_local_discard(void) {
#if defined(_WIN32)
    return -1;
#else
    int fd = socket(AF_INET, SOCK_DGRAM, 0);
    if (fd < 0) return -1;
    struct sockaddr_in addr;
    rt_core_sockaddr_loopback(9, &addr);
    sendto(fd, "x", 1, 0, (struct sockaddr*)&addr, sizeof(addr));
    close(fd);
    return 0;
#endif
}

int64_t rt_net_http_plain_local_probe(void) {
#if defined(_WIN32)
    return -1;
#else
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return -1;
    struct sockaddr_in addr;
    rt_core_sockaddr_loopback(80, &addr);
    if (connect(fd, (struct sockaddr*)&addr, sizeof(addr)) == 0) {
        write(fd, "GET / HTTP/1.0\r\n\r\n", 18);
    }
    close(fd);
    return 0;
#endif
}

/* ================================================================
 * Memory Operations
 * ================================================================ */

/* Struct field accesses are emitted as direct native loads/stores, so a
 * non-null corrupt receiver must be rejected before Cranelift dereferences it.
 * Keep a dedicated, bounded allocation table: this avoids probing candidate
 * addresses and keeps validation O(1) on the field-access hot path. */
typedef struct RtStructAllocation {
    uintptr_t ptr;
    size_t bytes;
} RtStructAllocation;

#define RT_STRUCT_ALLOC_TOMBSTONE ((uintptr_t)1)
#define RT_STRUCT_ALLOC_MAX_CAP ((size_t)1 << 22)

static RtStructAllocation* rt_struct_allocs = NULL;
static size_t rt_struct_alloc_cap = 0;
static size_t rt_struct_alloc_len = 0;
static size_t rt_struct_alloc_tombs = 0;
#if defined(_WIN32)
static SRWLOCK rt_struct_alloc_lock = SRWLOCK_INIT;
#else
static pthread_rwlock_t rt_struct_alloc_lock = PTHREAD_RWLOCK_INITIALIZER;
#endif

static void rt_struct_alloc_lock_acquire(void) {
#if defined(_WIN32)
    AcquireSRWLockExclusive(&rt_struct_alloc_lock);
#else
    pthread_rwlock_wrlock(&rt_struct_alloc_lock);
#endif
}

static void rt_struct_alloc_lock_release(void) {
#if defined(_WIN32)
    ReleaseSRWLockExclusive(&rt_struct_alloc_lock);
#else
    pthread_rwlock_unlock(&rt_struct_alloc_lock);
#endif
}

static void rt_struct_alloc_read_lock_acquire(void) {
#if defined(_WIN32)
    AcquireSRWLockShared(&rt_struct_alloc_lock);
#else
    pthread_rwlock_rdlock(&rt_struct_alloc_lock);
#endif
}

static void rt_struct_alloc_read_lock_release(void) {
#if defined(_WIN32)
    ReleaseSRWLockShared(&rt_struct_alloc_lock);
#else
    pthread_rwlock_unlock(&rt_struct_alloc_lock);
#endif
}

static int rt_struct_alloc_insert_raw(uintptr_t ptr, size_t bytes) {
    size_t mask = rt_struct_alloc_cap - 1;
    size_t i = rt_core_immortal_hash_ptr(ptr) & mask;
    size_t first_tomb = SIZE_MAX;
    for (;;) {
        uintptr_t entry = rt_struct_allocs[i].ptr;
        if (entry == 0) {
            size_t target = first_tomb == SIZE_MAX ? i : first_tomb;
            rt_struct_allocs[target] = (RtStructAllocation){ptr, bytes};
            if (first_tomb != SIZE_MAX) rt_struct_alloc_tombs--;
            rt_struct_alloc_len++;
            return 1;
        }
        if (entry == RT_STRUCT_ALLOC_TOMBSTONE) {
            if (first_tomb == SIZE_MAX) first_tomb = i;
        } else if (entry == ptr) {
            rt_struct_allocs[i].bytes = bytes;
            return 1;
        }
        i = (i + 1) & mask;
    }
}

static int rt_struct_alloc_resize(size_t next_cap) {
    if (next_cap > RT_STRUCT_ALLOC_MAX_CAP ||
            next_cap > SIZE_MAX / sizeof(RtStructAllocation)) return 0;
    RtStructAllocation* fresh = (RtStructAllocation*)calloc(
        next_cap, sizeof(RtStructAllocation));
    if (!fresh) return 0;
    RtStructAllocation* old = rt_struct_allocs;
    size_t old_cap = rt_struct_alloc_cap;
    rt_struct_allocs = fresh;
    rt_struct_alloc_cap = next_cap;
    rt_struct_alloc_len = 0;
    rt_struct_alloc_tombs = 0;
    for (size_t i = 0; i < old_cap; i++) {
        uintptr_t ptr = old[i].ptr;
        if (ptr != 0 && ptr != RT_STRUCT_ALLOC_TOMBSTONE) {
            rt_struct_alloc_insert_raw(ptr, old[i].bytes);
        }
    }
    free(old);
    return 1;
}

static int rt_struct_alloc_register(void* ptr, size_t bytes) {
    int ok = 0;
    if (!ptr) return 0;
    rt_struct_alloc_lock_acquire();
    if (rt_struct_alloc_cap == 0) {
        ok = rt_struct_alloc_resize(256);
    } else {
        ok = 1;
    }
    if (ok && (rt_struct_alloc_len + rt_struct_alloc_tombs + 1) * 10
            >= rt_struct_alloc_cap * 7) {
        if (rt_struct_alloc_cap < RT_STRUCT_ALLOC_MAX_CAP) {
            ok = rt_struct_alloc_resize(rt_struct_alloc_cap * 2);
        } else if (rt_struct_alloc_tombs > rt_struct_alloc_len / 4) {
            ok = rt_struct_alloc_resize(rt_struct_alloc_cap);
        } else if (rt_struct_alloc_len + 1 >= rt_struct_alloc_cap) {
            ok = 0;
        }
    }
    if (ok) ok = rt_struct_alloc_insert_raw((uintptr_t)ptr, bytes);
    rt_struct_alloc_lock_release();
    return ok;
}

static void rt_struct_alloc_unregister(void* ptr) {
    if (!ptr) return;
    rt_struct_alloc_lock_acquire();
    if (rt_struct_alloc_cap != 0) {
        size_t mask = rt_struct_alloc_cap - 1;
        size_t i = rt_core_immortal_hash_ptr((uintptr_t)ptr) & mask;
        for (;;) {
            uintptr_t entry = rt_struct_allocs[i].ptr;
            if (entry == 0) break;
            if (entry == (uintptr_t)ptr) {
                rt_struct_allocs[i] = (RtStructAllocation){RT_STRUCT_ALLOC_TOMBSTONE, 0};
                rt_struct_alloc_len--;
                rt_struct_alloc_tombs++;
                break;
            }
            i = (i + 1) & mask;
        }
    }
    rt_struct_alloc_lock_release();
}

static int rt_struct_alloc_lookup_size(void* ptr, size_t* bytes_out) {
    int found = 0;
    if (!ptr) return 0;
    rt_struct_alloc_read_lock_acquire();
    if (rt_struct_alloc_cap != 0) {
        size_t mask = rt_struct_alloc_cap - 1;
        size_t i = rt_core_immortal_hash_ptr((uintptr_t)ptr) & mask;
        for (;;) {
            uintptr_t entry = rt_struct_allocs[i].ptr;
            if (entry == 0) break;
            if (entry == (uintptr_t)ptr) {
                *bytes_out = rt_struct_allocs[i].bytes;
                found = 1;
                break;
            }
            i = (i + 1) & mask;
        }
    }
    rt_struct_alloc_read_lock_release();
    return found;
}

void* rt_alloc(int64_t size) {
    if (size < 0) return NULL;
    if (rt_mem_guard_should_sample((size_t)size)) {
        void* guarded = rt_mem_guard_alloc_sampled((size_t)size);
        if (guarded != NULL) {
            /* A sampled slot is still a raw block handed to the caller, so it
             * must enter the core transient raw registry exactly like the
             * malloc path below. Skipping it made the registry's view of a
             * block depend on a sampling coin flip: rt_transient_heap_promote
             * could not classify a tagged raw root that happened to be
             * sampled, so it refused, and a promoted live graph was reported
             * unpromotable under SIMPLE_MEM_GUARD_RATE. */
            if (!rt_core_transient_raw_register(guarded, (size_t)size)) {
                rt_mem_guard_free_sampled(guarded);
                return NULL;
            }
            return guarded;
        }
        /* mmap/mprotect failed (or the slot table is full) -- fall through
         * to the normal allocator below rather than returning NULL for a
         * sampling decision that isn't itself an OOM. */
    }
    void* ptr = malloc((size_t)size);
    if (ptr && !rt_core_transient_raw_register(ptr, (size_t)size)) {
        free(ptr);
        return NULL;
    }
    return ptr;
}

void* rt_struct_alloc(int64_t size) {
    if (size < 0) return NULL;
    void* ptr = rt_alloc(size);
    if (ptr && !rt_struct_alloc_register(ptr, (size_t)size)) {
        rt_free(ptr);
        return NULL;
    }
    return ptr;
}

int8_t rt_struct_receiver_valid(int64_t receiver, int64_t byte_offset, int64_t access_width) {
    if (receiver == 0 || byte_offset < 0 || access_width <= 0) return 0;
    uintptr_t ptr = (uintptr_t)(((uint64_t)receiver) & ~RT_VALUE_TAG_MASK);
    if (ptr == 0) return 0;

    int8_t valid = 0;
    rt_struct_alloc_read_lock_acquire();
    if (rt_struct_alloc_cap != 0) {
        size_t mask = rt_struct_alloc_cap - 1;
        size_t i = rt_core_immortal_hash_ptr(ptr) & mask;
        for (;;) {
            uintptr_t entry = rt_struct_allocs[i].ptr;
            if (entry == 0) break;
            if (entry == ptr) {
                size_t offset = (size_t)byte_offset;
                size_t width = (size_t)access_width;
                size_t bytes = rt_struct_allocs[i].bytes;
                valid = offset <= bytes && width <= bytes - offset;
                break;
            }
            i = (i + 1) & mask;
        }
    }
    rt_struct_alloc_read_lock_release();
    return valid;
}

void* rt_realloc(void* ptr, int64_t size) {
    if (size < 0) return NULL;
    if (!ptr) return rt_alloc(size);
    size_t struct_bytes = 0;
    if (rt_struct_alloc_lookup_size(ptr, &struct_bytes)) {
        if (size == 0) {
            rt_free(ptr);
            return NULL;
        }
        void* next = rt_struct_alloc(size);
        if (!next) return NULL;
        memcpy(next, ptr, struct_bytes < (size_t)size ? struct_bytes : (size_t)size);
        rt_free(ptr);
        return next;
    }
    if (rt_mem_guard_is_slot(ptr)) {
        /* A guard slot is a page-aligned mmap mapping, not a libc heap
         * chunk -- realloc()ing it directly would be undefined behaviour.
         * Emulate realloc instead: allocate fresh through the normal
         * allocator (re-sampling a slot that's about to be resized isn't
         * required), copy the overlap, then free the OLD slot through the
         * guard path so a UAF on the stale pointer still traps. */
        RtMemGuardSlot* slot = rt_mem_guard_find(ptr);
        size_t old_size = slot ? slot->size : 0;
        if (size == 0) {
            rt_mem_guard_free_sampled(ptr);
            return NULL;
        }
        void* next = malloc((size_t)size);
        if (!next) return NULL;
        if (!rt_core_transient_raw_register(next, (size_t)size)) {
            free(next);
            return NULL;
        }
        memcpy(next, ptr, old_size < (size_t)size ? old_size : (size_t)size);
        rt_mem_guard_free_sampled(ptr);
        return next;
    }
    RtCoreTransientRawAlloc* tracked = rt_core_transient_raw_lookup((uintptr_t)ptr);
    if (!tracked) return realloc(ptr, (size_t)size);
    if (size == 0) {
        rt_core_transient_raw_erase(ptr);
        free(ptr);
        return NULL;
    }
    size_t old_size = tracked->bytes & RT_CORE_TRANSIENT_RAW_SIZE_MASK;
    int owned = (tracked->bytes & RT_CORE_TRANSIENT_RAW_OWNED_BIT) != 0;
    void* next = malloc((size_t)size);
    if (!next) return NULL;
    if (!rt_core_transient_raw_register_state(next, (size_t)size, owned)) {
        free(next);
        return NULL;
    }
    memcpy(next, ptr, old_size < (size_t)size ? old_size : (size_t)size);
    rt_core_transient_raw_erase(ptr);
    free(ptr);
    return next;
}

void rt_free(void* ptr) {
    rt_struct_alloc_unregister(ptr);
    if (rt_mem_guard_is_slot(ptr)) {
        rt_mem_guard_free_sampled(ptr);
        return;
    }
    rt_core_transient_raw_erase(ptr);
    free(ptr);
}

int64_t rt_mem_guard_stats(void) {
    return rt_mem_guard_stats_native();
}

void* rt_memcpy(void* dst, const void* src, int64_t n) {
    return memcpy(dst, src, (size_t)n);
}

void* copy_mem(void* dst, const void* src, int64_t n) {
    return rt_memcpy(dst, src, n);
}

void* rt_memset(void* dst, int8_t val, int64_t n) {
    return memset(dst, (int)val, (size_t)n);
}

int64_t rt_memcmp(const void* a, const void* b, int64_t n) {
    return (int64_t)memcmp(a, b, (size_t)n);
}

void rt_invlpg(uint64_t addr) {
    (void)addr;
}

uint64_t unsafe_addr_of(int64_t value) {
    return (uint64_t)value;
}

static uint64_t rt_host_cr3;

uint64_t rt_read_cr3(void) {
    return rt_host_cr3;
}

void rt_write_cr3(uint64_t value) {
    rt_host_cr3 = value;
}

uint64_t rt_read_cr3_raw(void) {
    return rt_read_cr3();
}

void rt_write_cr3_raw(uint64_t value) {
    rt_write_cr3(value);
}

int64_t rt_volatile_read_u8(int64_t addr) {
    return *(volatile uint8_t*)(uintptr_t)addr;
}

int64_t rt_volatile_read_u16(int64_t addr) {
    return *(volatile uint16_t*)(uintptr_t)addr;
}

int64_t rt_volatile_read_u32(int64_t addr) {
    return *(volatile uint32_t*)(uintptr_t)addr;
}

int64_t rt_volatile_read_u64(int64_t addr) {
    return (int64_t)*(volatile uint64_t*)(uintptr_t)addr;
}

void rt_volatile_write_u8(int64_t addr, int64_t value) {
    *(volatile uint8_t*)(uintptr_t)addr = (uint8_t)value;
}

void rt_volatile_write_u16(int64_t addr, int64_t value) {
    *(volatile uint16_t*)(uintptr_t)addr = (uint16_t)value;
}

void rt_volatile_write_u32(int64_t addr, int64_t value) {
    *(volatile uint32_t*)(uintptr_t)addr = (uint32_t)value;
}

void rt_volatile_write_u64(int64_t addr, int64_t value) {
    *(volatile uint64_t*)(uintptr_t)addr = (uint64_t)value;
}

void rt_memory_barrier(void) {
    __atomic_thread_fence(__ATOMIC_SEQ_CST);
}

double rt_math_pow(double base, double exponent) {
    return pow(base, exponent);
}

/* ================================================================
 * DMA Operations (hosted fallback — FR-DRIVER-0005)
 * ================================================================
 *
 * Baremetal supplies rt_dma_* via src/runtime/startup/baremetal/dma.c
 * + dma_<arch>.c. The hosted path is functional-not-coherent: we
 * page-align via posix_memalign so drivers that expect page-aligned
 * DMA buffers run in unit tests, and sync ops collapse to a compiler
 * barrier because userspace talks to simulated devices via memcpy.
 */

#define RT_DMA_HOST_MAX_SLOTS 32
#define RT_DMA_HOST_PAGE_SIZE 4096

struct rt_dma_host_slot {
    void    *virt;
    int64_t  size;
    int      in_use;
};

static struct rt_dma_host_slot g_rt_dma_host_slots[RT_DMA_HOST_MAX_SLOTS];

#if !defined(_WIN32)
/* posix_memalign is in POSIX-2001; declare explicitly so this file
 * compiles under strict `-std=c11` without a feature-test macro. */
extern int posix_memalign(void **memptr, size_t alignment, size_t size);
#endif

static void* rt_dma_aligned_alloc(size_t alignment, size_t size) {
#if defined(_WIN32)
    return _aligned_malloc(size, alignment);
#else
    void* p = NULL;
    if (posix_memalign(&p, alignment, size) != 0) return NULL;
    return p;
#endif
}

static void rt_dma_aligned_free(void* p) {
#if defined(_WIN32)
    _aligned_free(p);
#else
    free(p);
#endif
}

int64_t rt_dma_alloc(int64_t size, int32_t dir_raw) {
    (void)dir_raw;
    if (size <= 0) return -1;

    int slot = -1;
    for (int i = 0; i < RT_DMA_HOST_MAX_SLOTS; i++) {
        if (!g_rt_dma_host_slots[i].in_use) { slot = i; break; }
    }
    if (slot < 0) return -1;

    void *p = rt_dma_aligned_alloc(RT_DMA_HOST_PAGE_SIZE, (size_t)size);
    if (!p) {
        return -1;
    }
    g_rt_dma_host_slots[slot].virt   = p;
    g_rt_dma_host_slots[slot].size   = size;
    g_rt_dma_host_slots[slot].in_use = 1;
    return (int64_t)slot;
}

void rt_dma_free(int64_t handle) {
    if (handle < 0 || handle >= RT_DMA_HOST_MAX_SLOTS) return;
    if (g_rt_dma_host_slots[handle].in_use) {
        rt_dma_aligned_free(g_rt_dma_host_slots[handle].virt);
    }
    g_rt_dma_host_slots[handle].virt   = NULL;
    g_rt_dma_host_slots[handle].size   = 0;
    g_rt_dma_host_slots[handle].in_use = 0;
}

int64_t rt_dma_virt_of(int64_t handle) {
    if (handle < 0 || handle >= RT_DMA_HOST_MAX_SLOTS) return 0;
    if (!g_rt_dma_host_slots[handle].in_use) return 0;
    return (int64_t)(uintptr_t)g_rt_dma_host_slots[handle].virt;
}

int64_t rt_dma_phys_of(int64_t handle) {
    /* Userspace has no physical addresses; return virt so drivers
     * that program a DMA-physical register at least see a stable,
     * unique address. Not safe for real hardware — by design. */
    return rt_dma_virt_of(handle);
}

void rt_dma_sync_for_device(int64_t handle, int32_t dir_raw) {
    (void)handle;
    (void)dir_raw;
    __asm__ volatile ("" ::: "memory");  /* compiler barrier only */
}

void rt_dma_sync_for_cpu(int64_t handle, int32_t dir_raw) {
    (void)handle;
    (void)dir_raw;
    __asm__ volatile ("" ::: "memory");
}

int64_t rt_dma_cache_line_size(void) {
    /* 64 B is the x86_64 / arm64 default and covers every current
     * hosted development target. Real baremetal overrides this via
     * the per-arch dma_<arch>.c. */
    return 64;
}

/* ================================================================
 * String Operations
 * ================================================================ */

int64_t rt_strlen(const char* s) {
    return spl_str_len(s);
}

char* rt_strcat(const char* a, const char* b) {
    return spl_str_concat(a, b);
}

/* Concat-drop fix: `rt_strcat` above returns a RAW malloc'd char* with no
 * RtCoreString tag. Downstream consumers that tag-validate their operands
 * (e.g. the Rust-side extract_rt_string_array feeding rt_native_build,
 * src/compiler_rust/compiler/src/pipeline/native_project/lib.rs:68-94)
 * silently DROP such untagged values -- e.g. a `[text]` array holding one
 * concat-produced element and one plain literal loses the concat element on
 * that path. rt_strcat_tagged is the tagged-result counterpart used by the
 * native `+` binop lowering (expr_dispatch.spl bin_is_str_concat): it
 * normalizes both operands via the same tagged-or-raw autodetection
 * rt_interp_cstr already uses (bug #136), then builds a single freshly
 * malloc'd RtCoreString (same layout/tag rt_string_new produces) directly
 * from the two source buffers -- one copy, no extra rt_string_new wrap. Do
 * NOT change rt_strcat itself: its existing raw-char* consumers (string
 * interpolation, [...].join in method_calls_literals.spl) expect a raw
 * pointer. */
int64_t rt_strcat_tagged(int64_t a, int64_t b) {
    const char* left = rt_interp_cstr(a);
    const char* right = rt_interp_cstr(b);
    size_t left_len = left ? strlen(left) : 0;
    size_t right_len = right ? strlen(right) : 0;
    size_t total = left_len + right_len;

    RtCoreString* out = (RtCoreString*)malloc(sizeof(RtCoreString) + total + 1);
    if (!out) return rt_core_nil();
    out->kind = RT_VALUE_HEAP_STRING;
    out->reserved = 0;
    out->len = (uint64_t)total;
    if (left_len > 0) memcpy(out->data, left, left_len);
    if (right_len > 0) memcpy(out->data + left_len, right, right_len);
    out->data[total] = '\0';
    if (!rt_core_register_string(out)) {
        free(out);
        return rt_core_nil();
    }
    return (int64_t)(((uint64_t)(uintptr_t)out) | RT_VALUE_TAG_HEAP);
}

char* rt_substr(const char* s, int64_t start, int64_t len) {
    return spl_str_slice(s, start, start + len);
}

int64_t rt_strfind(const char* s, const char* needle) {
    return spl_str_index_of(s, needle);
}

char* rt_strreplace(const char* s, const char* old_s, const char* new_s) {
    return spl_str_replace(s, old_s, new_s);
}

SplArray* rt_strsplit(const char* s, const char* delim) {
    SplArray* out = rt_array_new(4);
    if (!out || !s) return out;
    if (!delim || !*delim) {
        rt_array_push(out, rt_string_new((const uint8_t*)s, (uint64_t)strlen(s)));
        return out;
    }
    size_t delim_len = strlen(delim);
    const char* start = s;
    const char* hit = NULL;
    while ((hit = strstr(start, delim)) != NULL) {
        rt_array_push(out, rt_string_new((const uint8_t*)start, (uint64_t)(hit - start)));
        start = hit + delim_len;
    }
    rt_array_push(out, rt_string_new((const uint8_t*)start, (uint64_t)strlen(start)));
    return out;
}

int64_t rt_strcmp(const char* a, const char* b) {
    return (int64_t)spl_str_cmp(a, b);
}

/* ================================================================
 * Array Operations
 * ================================================================ */

static SplArray* rt_core_array_new_fill(int64_t cap, uint8_t flags, int zero_items) {
    int64_t actual_cap = cap > 4 ? cap : 4;
    if (actual_cap < 0 || actual_cap > RT_CORE_ARRAY_MAX_CAP ||
        actual_cap > INT64_MAX / (int64_t)sizeof(int64_t)) {
        return NULL;
    }
    RtCoreArray* a = (RtCoreArray*)calloc(1, sizeof(RtCoreArray));
    if (!a) return NULL;
    a->kind = RT_VALUE_HEAP_ARRAY;
    a->flags = flags;
    a->cap = actual_cap;
    size_t elem_size = (flags & RT_CORE_ARRAY_FLAG_BYTES) ? sizeof(uint8_t) : sizeof(int64_t);
    a->data = zero_items ? calloc((size_t)actual_cap, elem_size) : malloc((size_t)actual_cap * elem_size);
    if (!a->data) {
        free(a);
        return NULL;
    }
    if (!rt_core_register_array(a)) {
        free(a->data);
        free(a);
        return NULL;
    }
    return (SplArray*)(((uintptr_t)a) | RT_VALUE_TAG_HEAP);
}

static SplArray* rt_core_array_new(int64_t cap, uint8_t flags) {
    return rt_core_array_new_fill(cap, flags, 1);
}

SplArray* rt_array_new(int64_t cap) {
    return rt_core_array_new(cap, 0);
}

SplArray* rt_array_new_uninit(int64_t cap) {
    return rt_core_array_new_fill(cap, 0, 0);
}

SplArray* rt_array_new_with_cap_u64(int64_t cap) {
    return rt_core_array_new(cap, RT_CORE_ARRAY_FLAG_U64_PACKED);
}

void rt_array_free(SplArray* value) {
    RtCoreArray* array = rt_core_as_registered_array((int64_t)(uintptr_t)value);
    if (!array || !rt_core_unregister_array(array)) return;
    free(array->data);
    free(array);
}

/* ===========================================================================
 * rt_array_free_deep -- deep (recursive) array free
 * ===========================================================================
 *
 * rt_array_free above is SHALLOW: it releases the outer buffer and the header
 * and leaks every heap element the buffer pointed at. That makes the confirmed
 * eviction leaks over `[u8]` / `[u32]` / element-bearing arrays inexpressible,
 * since the payload is exactly what the shallow free refuses to touch.
 *
 * Contract -- identical bias to rt_string_free: return 1 only if the object was
 * reclaimed, 0 if refused, and REFUSE rather than trust the caller. There is no
 * GC and no refcount here, so nothing can prove a pointer is unaliased; every
 * rule below is a conservative approximation that errs toward leaking.
 *
 * PARTIAL-FREE POLICY: ALL-OR-NOTHING, decided in two phases.
 *   Phase 1 walks the whole structure READ-ONLY and classifies every reachable
 *   node, freeing nothing. If any node is not provably freeable the call
 *   returns 0 having freed NOTHING AT ALL. Only a fully-provable structure
 *   reaches phase 2, which then frees every planned node.
 *
 *   Justification for rejecting the "free the outer buffer anyway" alternative:
 *   a refused element is reachable ONLY through the buffer that holds it. Free
 *   the buffer and that element becomes simultaneously unreachable AND
 *   unfreeable -- a permanent leak that no later, smarter caller can ever
 *   reclaim, plus a silently corrupted registry accounting. Refusing also
 *   leaks, but reversibly: the caller still holds the root and can retry, free
 *   the elements individually first, or fall back to rt_array_free. A
 *   reversible leak strictly dominates an irreversible one, so refusal wins.
 *   Because no partial state can exist, the return value is an honest binary:
 *   1 == the entire structure is gone, 0 == nothing was touched.
 *
 * What counts as provably freeable:
 *   - BYTES / U64_PACKED arrays: the payload is packed uint8_t / raw u64 with
 *     no heap references BY CONSTRUCTION, so the element scan is skipped
 *     entirely. This is the trivially-safe tier and covers `[u8]` payloads such
 *     as GlyphBitmap.pixels.
 *   - a generic array whose every element is an immediate (TAG_INT, TAG_FLOAT,
 *     TAG_SPECIAL/nil, or any value below 4096) -- nothing to free, nothing to
 *     strand. Covers `[u32]` and ordinary `[i64]`.
 *   - a non-shared registered heap string element (rt_string_free's own rule:
 *     RT_CORE_STRING_FLAG_SHARED marks the process-wide short-string cache and
 *     the literal intern table, whose objects are handed to unrelated holders,
 *     so freeing one corrupts all of them).
 *   - a registered array element, recursively, under all of these same rules.
 *   - a registered dict element, recursively (see rt_dict_free_deep below).
 *     Dicts joined this tier on 2026-08-06; before that they were refused for
 *     want of a free primitive.
 *
 * Everything else refuses the WHOLE call, in particular:
 *   - any HEAP-tagged element that is not a registered string, registered
 *     array or registered dict. That set includes registered enums / closures /
 *     mutexes / heap-boxed f64 (owned, but with no free path here -- freeing
 *     the buffer would strand them),
 *     foreign
 *     pointers, and raw i64 payloads that merely alias the tag bits. The last
 *     case is a FALSE refusal for a generic array carrying raw i64s >= 4096
 *     with low bits 0b001 -- accepted deliberately: a false refusal leaks (the
 *     status quo), a false accept corrupts every other holder.
 *   - ALIASING AND CYCLES. RuntimeValue is Copy over a u64, so an element may
 *     be the array itself or appear twice. Phase 1 keeps a `seen` pointer set;
 *     the second sighting of any node refuses the whole call. This proves the
 *     reachable structure is a TREE, which is what makes freeing it bottom-up
 *     safe -- but note it can only rule out aliases INTERNAL to the structure.
 *
 * LIMIT, stated plainly: an interior node aliased from OUTSIDE the structure is
 * undetectable here, exactly as rt_string_free cannot detect a second holder of
 * its string. The caller must own the whole subtree, not merely the root. The
 * refusals above shrink the blast radius; they do not remove that obligation.
 * Likewise not thread-safe against a concurrent free of the same objects.
 *
 * SECOND LIMIT, recorded 2026-08-06 because it is easy to misread the LEAF rule
 * as "safe by construction": a class/struct INSTANCE is invisible to this
 * classifier. On the C-native lane an instance is emitted as a bare
 * `call ptr @rt_alloc(i64 n*8)` block (70.backend/.../aggregate_intrinsics.spl,
 * the Aggregate/Struct lowering) -- it carries NO kind header, is NOT
 * heap-tagged, and is NOT in any registry (rt_alloc only records a block while
 * a transient array scope is active, runtime_native.c
 * rt_core_transient_raw_register_state). Such a pointer is >= 4096 with low
 * bits 0b000, so it lands in the FIRST branch below and classifies as LEAF --
 * i.e. "nothing to free", which is true of the WORD but false of the block it
 * points at. Freeing a container of instances therefore reclaims the container
 * and IRREVERSIBLY strands every instance. This cannot be fixed inside the
 * classifier: an untagged i64 is genuinely indistinguishable from an integer.
 * It is fixable only upstream, by giving rt_alloc'd aggregates a kind header or
 * an unconditional registration. Until then, a caller must not hand this
 * primitive any structure whose leaves are object instances. See
 * doc/08_tracking/bug/bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md
 */

#define RT_CORE_DEEP_FREE_LEAF 0
#define RT_CORE_DEEP_FREE_STRING 1
#define RT_CORE_DEEP_FREE_ARRAY 2
#define RT_CORE_DEEP_FREE_REFUSE 3
#define RT_CORE_DEEP_FREE_DICT 4

/* Bounds the planner's own memory; exceeding it refuses rather than grows. */
#define RT_CORE_DEEP_FREE_MAX_NODES ((size_t)1 << 22)

typedef struct RtCoreDeepFreeNode {
    void* ptr;
    int kind; /* RT_CORE_DEEP_FREE_STRING or RT_CORE_DEEP_FREE_ARRAY */
} RtCoreDeepFreeNode;

typedef struct RtCoreDeepFreePlan {
    RtCoreDeepFreeNode* nodes; /* also the BFS worklist, in free order */
    size_t len;
    size_t cap;
    uintptr_t* seen; /* open-addressed pointer set, 0 = empty; no deletes, so */
    size_t seen_cap; /* no tombstones are needed (unlike the immortal table)  */
    size_t seen_len;
} RtCoreDeepFreePlan;

/* caller-local table, no lock needed */
static int rt_core_deep_free_seen_grow(RtCoreDeepFreePlan* plan) {
    size_t new_cap = plan->seen_cap == 0 ? 256 : plan->seen_cap * 2;
    if (new_cap > SIZE_MAX / sizeof(uintptr_t)) return 0;
    uintptr_t* fresh = (uintptr_t*)calloc(new_cap, sizeof(uintptr_t));
    if (!fresh) return 0;
    size_t mask = new_cap - 1;
    for (size_t i = 0; i < plan->seen_cap; i++) {
        uintptr_t e = plan->seen[i];
        if (e == 0) continue;
        size_t j = rt_core_immortal_hash_ptr(e) & mask;
        while (fresh[j] != 0) j = (j + 1) & mask;
        fresh[j] = e;
    }
    free(plan->seen);
    plan->seen = fresh;
    plan->seen_cap = new_cap;
    return 1;
}

/* 1 = newly inserted, 0 = already present (alias or cycle), -1 = out of memory */
static int rt_core_deep_free_seen_insert(RtCoreDeepFreePlan* plan, uintptr_t p) {
    if ((plan->seen_len + 1) * 10 >= plan->seen_cap * 7) {
        if (!rt_core_deep_free_seen_grow(plan)) return -1;
    }
    size_t mask = plan->seen_cap - 1;
    size_t i = rt_core_immortal_hash_ptr(p) & mask;
    for (;;) {
        uintptr_t e = plan->seen[i];
        if (e == 0) {
            plan->seen[i] = p;
            plan->seen_len++;
            return 1;
        }
        if (e == p) return 0;
        i = (i + 1) & mask;
    }
}

static int rt_core_deep_free_plan_push(RtCoreDeepFreePlan* plan, void* ptr, int kind) {
    if (plan->len == plan->cap) {
        size_t next_cap = plan->cap == 0 ? 32 : plan->cap * 2;
        if (next_cap > RT_CORE_DEEP_FREE_MAX_NODES) return 0;
        RtCoreDeepFreeNode* fresh = (RtCoreDeepFreeNode*)realloc(
            plan->nodes, next_cap * sizeof(RtCoreDeepFreeNode));
        if (!fresh) return 0;
        plan->nodes = fresh;
        plan->cap = next_cap;
    }
    plan->nodes[plan->len].ptr = ptr;
    plan->nodes[plan->len].kind = kind;
    plan->len++;
    return 1;
}

/* Classify one element slot. Every dereference is gated on a registry
 * membership test (a PURE POINTER COMPARISON), so a raw i64 that merely aliases
 * the HEAP tag is never dereferenced -- same guard rt_core_as_string and
 * rt_core_as_enum use. Requiring RT_VALUE_TAG_HEAP (rather than also accepting
 * the untagged array form rt_core_as_array tolerates) additionally keeps a
 * TAG_INT payload from ever being mistaken for an array pointer. */
static int rt_core_deep_free_classify(int64_t value, void** out_ptr) {
    uintptr_t raw = (uintptr_t)value;
    *out_ptr = NULL;
    if (raw < 4096) return RT_CORE_DEEP_FREE_LEAF;
    if ((raw & RT_VALUE_TAG_MASK) != RT_VALUE_TAG_HEAP) return RT_CORE_DEEP_FREE_LEAF;
    void* p = (void*)(raw & ~RT_VALUE_TAG_MASK);
    if (rt_core_is_registered_immortal_ptr(p)) {
        uint32_t kind = rt_core_registered_object_kind(p);
        if (kind == RT_VALUE_HEAP_ARRAY) {
            RtCoreArray* a = rt_core_as_array((int64_t)raw);
            if (!a) return RT_CORE_DEEP_FREE_REFUSE;
            *out_ptr = a;
            return RT_CORE_DEEP_FREE_ARRAY;
        }
        if (kind == RT_VALUE_HEAP_STRING) {
            RtCoreString* s = (RtCoreString*)p;
            if (s->reserved & RT_CORE_STRING_FLAG_SHARED) return RT_CORE_DEEP_FREE_REFUSE;
            *out_ptr = s;
            return RT_CORE_DEEP_FREE_STRING;
        }
        if (kind == RT_VALUE_HEAP_DICT) {
            /* Re-validate through rt_core_as_dict rather than trusting the kind
             * byte alone -- same belt-and-braces the array branch above applies
             * via rt_core_as_array. */
            RtCoreDict* d = rt_core_as_dict((int64_t)raw);
            if (!d) return RT_CORE_DEEP_FREE_REFUSE;
            *out_ptr = d;
            return RT_CORE_DEEP_FREE_DICT;
        }
    }
    return RT_CORE_DEEP_FREE_REFUSE;
}

/* Shared engine for rt_array_free_deep / rt_dict_free_deep / rt_free_deep.
 * `root` is an already-validated registry member and `root_kind` is its
 * RT_CORE_DEEP_FREE_* classification. Returns 1 if the entire reachable
 * structure was reclaimed, 0 if the call refused and freed NOTHING. */
static int64_t rt_core_deep_free_run(void* root, int root_kind) {
    RtCoreDeepFreePlan plan;
    plan.nodes = NULL;
    plan.len = 0;
    plan.cap = 0;
    plan.seen = NULL;
    plan.seen_cap = 0;
    plan.seen_len = 0;

    int refused = 0;
    if (rt_core_deep_free_seen_insert(&plan, (uintptr_t)root) != 1) refused = 1;
    if (!refused && !rt_core_deep_free_plan_push(&plan, root, root_kind)) refused = 1;

    /* Phase 1: read-only breadth-first classification. plan.nodes doubles as
     * the worklist, so this is iterative -- a deeply nested structure cannot
     * blow the C stack. One shared `seen` set spans ALL node kinds, so an alias
     * that crosses a type boundary (the same string reachable from both an
     * array element and a dict key) is caught exactly like a same-kind alias.
     * That is why dict support lives in this one planner rather than in a
     * separate primitive chained after it: two planners would each see a clean
     * tree and between them double-free the shared node. */
    for (size_t i = 0; !refused && i < plan.len; i++) {
        /* Every child slot is funnelled through this lambda-shaped block so the
         * array and dict walks cannot drift apart. */
        int64_t inline_slots[2];
        const int64_t* slots = NULL;
        int64_t slot_count = 0;

        if (plan.nodes[i].kind == RT_CORE_DEEP_FREE_ARRAY) {
            RtCoreArray* a = (RtCoreArray*)plan.nodes[i].ptr;
            if (a->flags & (RT_CORE_ARRAY_FLAG_BYTES | RT_CORE_ARRAY_FLAG_U64_PACKED)) continue;
            if (!a->data) continue;
            slots = (const int64_t*)a->data;
            slot_count = a->len;
        } else if (plan.nodes[i].kind != RT_CORE_DEEP_FREE_DICT) {
            continue; /* strings are leaves */
        }

        if (plan.nodes[i].kind == RT_CORE_DEEP_FREE_DICT) {
            RtCoreDict* d = (RtCoreDict*)plan.nodes[i].ptr;
            if (!d->entries) continue;
            /* Walk the whole slot table, not just `len` entries: empty and
             * tombstoned slots carry stale key/value words that must NOT be
             * followed, and occupied==1 is the only state whose words are live.
             * Both a key and a value are ordinary tagged values, so the key
             * gets exactly the same classification as the value -- a shared or
             * interned string key refuses the call rather than being freed out
             * from under the intern table. */
            for (int64_t s = 0; s < d->cap && !refused; s++) {
                RtCoreDictEntry* e = &d->entries[s];
                if (e->occupied != 1) continue;
                inline_slots[0] = e->key;
                inline_slots[1] = e->value;
                for (int k = 0; k < 2; k++) {
                    void* child = NULL;
                    int kind = rt_core_deep_free_classify(inline_slots[k], &child);
                    if (kind == RT_CORE_DEEP_FREE_LEAF) continue;
                    if (kind == RT_CORE_DEEP_FREE_REFUSE) { refused = 1; break; }
                    if (rt_core_deep_free_seen_insert(&plan, (uintptr_t)child) != 1) {
                        refused = 1;
                        break;
                    }
                    if (!rt_core_deep_free_plan_push(&plan, child, kind)) {
                        refused = 1;
                        break;
                    }
                }
            }
            continue;
        }

        for (int64_t k = 0; k < slot_count; k++) {
            void* child = NULL;
            int kind = rt_core_deep_free_classify(slots[k], &child);
            if (kind == RT_CORE_DEEP_FREE_LEAF) continue;
            if (kind == RT_CORE_DEEP_FREE_REFUSE) {
                refused = 1;
                break;
            }
            /* 0 = alias or cycle, -1 = planner out of memory: both refuse */
            if (rt_core_deep_free_seen_insert(&plan, (uintptr_t)child) != 1) {
                refused = 1;
                break;
            }
            if (!rt_core_deep_free_plan_push(&plan, child, kind)) {
                refused = 1;
                break;
            }
        }
    }

    /* Phase 2: commit. Reached only when every node is provably freeable, so no
     * partial state is observable. Freeing top-down is safe because phase 1
     * already copied out every child pointer. */
    if (!refused) {
        for (size_t i = 0; i < plan.len; i++) {
            if (plan.nodes[i].kind == RT_CORE_DEEP_FREE_ARRAY) {
                RtCoreArray* a = (RtCoreArray*)plan.nodes[i].ptr;
                if (rt_core_unregister_array(a)) {
                    free(a->data);
                    free(a);
                }
            } else if (plan.nodes[i].kind == RT_CORE_DEEP_FREE_DICT) {
                RtCoreDict* d = (RtCoreDict*)plan.nodes[i].ptr;
                if (rt_core_unregister_immortal_ptr(d)) {
                    free(d->entries);
                    free(d);
                }
            } else {
                RtCoreString* s = (RtCoreString*)plan.nodes[i].ptr;
                if (rt_core_unregister_string(s)) free(s);
            }
        }
    }

    free(plan.nodes);
    free(plan.seen);
    return refused ? 0 : 1;
}

int64_t rt_array_free_deep(int64_t value) {
    uintptr_t root_raw = (uintptr_t)value;
    if (root_raw < 4096) return 0;
    /* the root must be an explicitly heap-tagged, registered array; a string
     * root belongs to rt_string_free, not here */
    if ((root_raw & RT_VALUE_TAG_MASK) != RT_VALUE_TAG_HEAP) return 0;
    RtCoreArray* root = rt_core_as_registered_array(value);
    if (!root) return 0;
    return rt_core_deep_free_run(root, RT_CORE_DEEP_FREE_ARRAY);
}

/* ===========================================================================
 * rt_dict_free_deep -- deep (recursive) dict free
 * ===========================================================================
 *
 * The dict-shaped counterpart of rt_array_free_deep, sharing its planner and
 * therefore its contract CLAUSE FOR CLAUSE: two phases (read-only classify,
 * then commit), all-or-nothing (a refusal frees NOTHING), every dereference
 * gated on registry membership so a tag-aliasing raw i64 is never followed, and
 * one `seen` pointer set that refuses on any internal alias or cycle.
 *
 * Dict-specific clauses:
 *   - Keys are classified EXACTLY like values. A dict keyed by interned or
 *     short-cache strings therefore refuses, which is the correct answer: those
 *     strings belong to a process-wide table and freeing one corrupts every
 *     other holder.
 *   - Only occupied==1 slots are followed. Empty and tombstoned slots retain
 *     stale key/value words from a previous occupant; following them would
 *     free memory the dict no longer owns.
 *   - The entries buffer is a flat calloc'd array of RtCoreDictEntry, freed in
 *     phase 2 with the header, exactly as rt_array_free frees data + header.
 *
 * NOT provided, deliberately: a SHALLOW rt_dict_free. rt_array_free's shallow
 * shape predates this contract and is kept only for compatibility; adding a new
 * shallow dict free would hand callers a primitive whose only outcome on a dict
 * of heap values is the irreversible strand the contract comment above argues
 * against by name. Callers wanting shallow semantics can empty the dict first.
 */
int64_t rt_dict_free_deep(int64_t value) {
    RtCoreDict* root = rt_core_as_dict(value);
    if (!root) return 0;
    return rt_core_deep_free_run(root, RT_CORE_DEEP_FREE_DICT);
}

/* Type-dispatching deep free. Accepts an array, a dict, or a non-shared
 * registered string root and applies the same all-or-nothing contract; refuses
 * anything else, including class/struct instances -- see the SECOND LIMIT note
 * on rt_array_free_deep for why an instance is not even identifiable here.
 *
 * This exists because the structures that actually need reclaiming are
 * heterogeneous nests (a Dict whose values are Dicts whose values hold arrays),
 * so a caller at the root cannot know statically which primitive to call, and
 * calling them in sequence would give each call its own `seen` set and lose the
 * cross-structure alias detection that makes the whole thing safe. */
int64_t rt_free_deep(int64_t value) {
    uintptr_t raw = (uintptr_t)value;
    if (raw < 4096) return 0;
    if ((raw & RT_VALUE_TAG_MASK) != RT_VALUE_TAG_HEAP) return 0;
    void* p = (void*)(raw & ~RT_VALUE_TAG_MASK);
    if (!rt_core_is_registered_immortal_ptr(p)) return 0;
    switch (rt_core_registered_object_kind(p)) {
        case RT_VALUE_HEAP_ARRAY:  return rt_array_free_deep(value);
        case RT_VALUE_HEAP_DICT:   return rt_dict_free_deep(value);
        case RT_VALUE_HEAP_STRING: return rt_string_free(value);
        default:                   return 0;
    }
}

/* Free a heap string. Returns 1 if the object was reclaimed, 0 if it was
 * refused. This runtime has no refcounting and RuntimeValue is Copy, so the
 * CALLER must own the only reference -- see
 * doc/09_report/stage4_deepfree_blocked_no_string_free_2026-07-25.md for which
 * values qualify (SourceFile.content does; an AST node's name does NOT).
 *
 * Refuses, rather than trusting the caller, when the object is: not a heap
 * string, owned by a process-wide cache (short-string or literal-intern), or
 * absent from the registry (already freed / never registered). A refusal leaks;
 * a wrong free corrupts every other holder, so the bias is deliberate. */
int64_t rt_string_free(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) return 0;
    if (s->reserved & RT_CORE_STRING_FLAG_SHARED) return 0;
    if (!rt_core_unregister_string(s)) return 0;
    free(s);
    return 1;
}

SplArray* rt_byte_array_new(uint64_t cap) {
    if (cap > (uint64_t)INT64_MAX) {
        return NULL;
    }
    return rt_core_array_new((int64_t)cap, RT_CORE_ARRAY_FLAG_BYTES);
}

SplArray* rt_byte_array_new_len(uint64_t len) {
    SplArray* a = rt_byte_array_new(len);
    RtCoreArray* array = rt_core_array_ptr(a);
    if (array) {
        array->len = (int64_t)len;
    }
    return a;
}

SplArray* rt_bytes_alloc(int64_t len) {
    if (len < 0) return NULL;
    return rt_byte_array_new_len((uint64_t)len);
}

int64_t rt_text_to_bytes(int64_t text_value) {
    RtCoreString* s = rt_core_as_string(text_value);
    uint64_t len = s ? s->len : 0;
    SplArray* arr = rt_byte_array_new_len(len);
    RtCoreArray* array = rt_core_array_ptr(arr);
    if (!array || !array->data) return (int64_t)(uintptr_t)arr;
    if (s && len > 0) {
        memcpy(array->data, s->data, (size_t)len);
    }
    return (int64_t)(uintptr_t)arr;
}

/* One-shot SHA-256 owner for the native core-C lane.  The Simple declaration
 * is `extern fn rt_tls13_sha256(data: [u8]) -> [u8]`, so both the argument and
 * return value use the lane's tagged i64/array ABI.  Keeping the implementation
 * beside RtCoreArray avoids a second, incompatible interpretation of [u8]. */
static uint32_t rt_sha256_rotr(uint32_t value, unsigned shift) {
    return (value >> shift) | (value << (32u - shift));
}

static void rt_sha256_compress(uint32_t state[8], const uint8_t block[64]) {
    static const uint32_t k[64] = {
        0x428a2f98u, 0x71374491u, 0xb5c0fbcfu, 0xe9b5dba5u,
        0x3956c25bu, 0x59f111f1u, 0x923f82a4u, 0xab1c5ed5u,
        0xd807aa98u, 0x12835b01u, 0x243185beu, 0x550c7dc3u,
        0x72be5d74u, 0x80deb1feu, 0x9bdc06a7u, 0xc19bf174u,
        0xe49b69c1u, 0xefbe4786u, 0x0fc19dc6u, 0x240ca1ccu,
        0x2de92c6fu, 0x4a7484aau, 0x5cb0a9dcu, 0x76f988dau,
        0x983e5152u, 0xa831c66du, 0xb00327c8u, 0xbf597fc7u,
        0xc6e00bf3u, 0xd5a79147u, 0x06ca6351u, 0x14292967u,
        0x27b70a85u, 0x2e1b2138u, 0x4d2c6dfcu, 0x53380d13u,
        0x650a7354u, 0x766a0abbu, 0x81c2c92eu, 0x92722c85u,
        0xa2bfe8a1u, 0xa81a664bu, 0xc24b8b70u, 0xc76c51a3u,
        0xd192e819u, 0xd6990624u, 0xf40e3585u, 0x106aa070u,
        0x19a4c116u, 0x1e376c08u, 0x2748774cu, 0x34b0bcb5u,
        0x391c0cb3u, 0x4ed8aa4au, 0x5b9cca4fu, 0x682e6ff3u,
        0x748f82eeu, 0x78a5636fu, 0x84c87814u, 0x8cc70208u,
        0x90befffau, 0xa4506cebu, 0xbef9a3f7u, 0xc67178f2u
    };
    uint32_t w[64];
    for (int i = 0; i < 16; i++) {
        size_t offset = (size_t)i * 4u;
        w[i] = ((uint32_t)block[offset] << 24) |
               ((uint32_t)block[offset + 1] << 16) |
               ((uint32_t)block[offset + 2] << 8) |
               (uint32_t)block[offset + 3];
    }
    for (int i = 16; i < 64; i++) {
        uint32_t s0 = rt_sha256_rotr(w[i - 15], 7) ^
                      rt_sha256_rotr(w[i - 15], 18) ^ (w[i - 15] >> 3);
        uint32_t s1 = rt_sha256_rotr(w[i - 2], 17) ^
                      rt_sha256_rotr(w[i - 2], 19) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16] + s0 + w[i - 7] + s1;
    }

    uint32_t a = state[0], b = state[1], c = state[2], d = state[3];
    uint32_t e = state[4], f = state[5], g = state[6], h = state[7];
    for (int i = 0; i < 64; i++) {
        uint32_t s1 = rt_sha256_rotr(e, 6) ^ rt_sha256_rotr(e, 11) ^
                      rt_sha256_rotr(e, 25);
        uint32_t choice = (e & f) ^ ((~e) & g);
        uint32_t t1 = h + s1 + choice + k[i] + w[i];
        uint32_t s0 = rt_sha256_rotr(a, 2) ^ rt_sha256_rotr(a, 13) ^
                      rt_sha256_rotr(a, 22);
        uint32_t majority = (a & b) ^ (a & c) ^ (b & c);
        uint32_t t2 = s0 + majority;
        h = g; g = f; f = e; e = d + t1;
        d = c; c = b; b = a; a = t1 + t2;
    }
    state[0] += a; state[1] += b; state[2] += c; state[3] += d;
    state[4] += e; state[5] += f; state[6] += g; state[7] += h;
}

int64_t rt_tls13_sha256(int64_t data_value) {
    RtCoreArray* input = rt_core_as_registered_array(data_value);
    if (!input || input->len < 0 || (input->len > 0 && !input->data)) {
        return rt_core_nil();
    }
    uint32_t state[8] = {
        0x6a09e667u, 0xbb67ae85u, 0x3c6ef372u, 0xa54ff53au,
        0x510e527fu, 0x9b05688cu, 0x1f83d9abu, 0x5be0cd19u
    };
    uint8_t block[128];
    uint64_t length = (uint64_t)input->len;
    uint64_t offset = 0;
    int packed_bytes = (input->flags & RT_CORE_ARRAY_FLAG_BYTES) != 0;

    while (length - offset >= 64u) {
        if (packed_bytes) {
            memcpy(block, (const uint8_t*)input->data + offset, 64u);
        } else {
            const int64_t* values = (const int64_t*)input->data;
            for (uint64_t i = 0; i < 64u; i++) {
                block[i] = (uint8_t)(rt_core_numeric_arg(values[offset + i]) & 0xff);
            }
        }
        rt_sha256_compress(state, block);
        offset += 64u;
    }

    size_t remaining = (size_t)(length - offset);
    memset(block, 0, sizeof(block));
    if (packed_bytes) {
        if (remaining > 0) {
            memcpy(block, (const uint8_t*)input->data + offset, remaining);
        }
    } else {
        const int64_t* values = (const int64_t*)input->data;
        for (size_t i = 0; i < remaining; i++) {
            block[i] = (uint8_t)(rt_core_numeric_arg(values[offset + i]) & 0xff);
        }
    }
    block[remaining] = 0x80u;
    size_t final_bytes = remaining < 56u ? 64u : 128u;
    uint64_t bit_length = length << 3;
    for (int i = 0; i < 8; i++) {
        block[final_bytes - 1u - (size_t)i] = (uint8_t)(bit_length >> (i * 8));
    }
    rt_sha256_compress(state, block);
    if (final_bytes == 128u) rt_sha256_compress(state, block + 64);

    SplArray* digest = rt_byte_array_new_len(32u);
    RtCoreArray* output = rt_core_array_ptr(digest);
    if (!output || !output->data) return rt_core_nil();
    for (int i = 0; i < 8; i++) {
        uint8_t* bytes = (uint8_t*)output->data + (size_t)i * 4u;
        bytes[0] = (uint8_t)(state[i] >> 24);
        bytes[1] = (uint8_t)(state[i] >> 16);
        bytes[2] = (uint8_t)(state[i] >> 8);
        bytes[3] = (uint8_t)state[i];
    }
    return (int64_t)(uintptr_t)digest;
}

int64_t rt_bytes_to_text(int64_t bytes_value) {
    RtCoreArray* array = rt_core_as_array(bytes_value);
    if (!array || !array->data || array->len <= 0) {
        return rt_string_new(NULL, 0);
    }
    return rt_string_new((const uint8_t*)array->data, (uint64_t)array->len);
}

int64_t rt_array_len(SplArray* a) {
    RtCoreArray* array = rt_core_array_ptr(a);
    return array ? array->len : 0;
}

int64_t rt_array_len_safe(int64_t value) {
    return rt_array_len((SplArray*)(uintptr_t)value);
}

/* Bytes-basis accessors for runtime_packed_span.c (SimplePackedSpanV1, F2).
 * They live here because RtCoreArray is private to this translation unit.
 * A non-bytes array is reported as "not a basis" (-1) and refused. */
int64_t rt_array_bytes_basis_len(SplArray* a) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return -1;
    if (!(array->flags & RT_CORE_ARRAY_FLAG_BYTES)) return -1;
    return array->len;
}

int64_t rt_array_bytes_basis_ptr(SplArray* a) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array || !array->data) return 0;
    if (!(array->flags & RT_CORE_ARRAY_FLAG_BYTES)) return 0;
    return (int64_t)(uintptr_t)array->data;
}

#if defined(__GNUC__) || defined(__clang__)
#define SPL_ARRAY_OWNER_WEAK __attribute__((weak))
#else
#define SPL_ARRAY_OWNER_WEAK
#endif

SPL_ARRAY_OWNER_WEAK int64_t rt_array_bytes_validate(int64_t value) {
    RtCoreArray* array = rt_core_as_registered_array(value);
    if (!array || array->len < 0) return -22;
    if (array->flags & (RT_CORE_ARRAY_FLAG_U64_PACKED | RT_CORE_ARRAY_FLAG_TUPLE)) return -22;
    if (array->flags & RT_CORE_ARRAY_FLAG_BYTES) return array->len;
    int64_t* items = (int64_t*)array->data;
    if (array->len > 0 && !items) return -22;
    for (int64_t i = 0; i < array->len; ++i) {
        if (!rt_core_is_int(items[i])) return -22;
        int64_t byte = rt_core_as_int(items[i]);
        if (byte < 0 || byte > 255) return -22;
    }
    return array->len;
}

SPL_ARRAY_OWNER_WEAK int64_t rt_array_bytes_copy_checked(int64_t value, uint8_t* out, int64_t capacity) {
    int64_t length = rt_array_bytes_validate(value);
    if (length < 0 || capacity < length || (length > 0 && !out)) return -22;
    RtCoreArray* array = rt_core_as_registered_array(value);
    if (array->flags & RT_CORE_ARRAY_FLAG_BYTES) {
        if (length > 0) memcpy(out, array->data, (size_t)length);
        return length;
    }
    int64_t* items = (int64_t*)array->data;
    for (int64_t i = 0; i < length; ++i) {
        out[i] = (uint8_t)rt_core_as_int(items[i]);
    }
    return length;
}

SPL_ARRAY_OWNER_WEAK int64_t rt_array_bytes_store_checked(int64_t value, const uint8_t* bytes, int64_t length) {
    int64_t capacity = rt_array_bytes_validate(value);
    if (capacity < 0 || length < 0 || length > capacity || (length > 0 && !bytes)) return -22;
    RtCoreArray* array = rt_core_as_registered_array(value);
    if (array->flags & RT_CORE_ARRAY_FLAG_BYTES) {
        if (length > 0) memcpy(array->data, bytes, (size_t)length);
        return length;
    }
    int64_t* items = (int64_t*)array->data;
    for (int64_t i = 0; i < length; ++i) {
        items[i] = rt_value_int(bytes[i]);
    }
    return length;
}

#undef SPL_ARRAY_OWNER_WEAK

int64_t rt_array_get(SplArray* a, int64_t idx) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 3;
    /* Native array ABI matches the Rust runtime: indices are raw i64 values. */
    if (idx < 0) idx = array->len + idx;
    if (idx < 0 || idx >= array->len) return 3;
    if (array->flags & RT_CORE_ARRAY_FLAG_BYTES) {
        return (int64_t)((uint8_t*)array->data)[idx];
    }
    return ((int64_t*)array->data)[idx];
}

int64_t rt_array_get_text(SplArray* a, int64_t idx) {
    return rt_array_get(a, idx);
}

int64_t rt_array_last(SplArray* a) {
    return rt_array_get(a, -1);
}

/* Returns 1 when the element was written, 0 when the array was null or the
 * (possibly negative) index was out of range. runtime_sffi.rs:257 declares
 * `&[I64, I64, I64] -> &[I8]` and src/runtime/simple_core/core_array.spl:182
 * already returns i8; this copy returning void meant the caller decoded an
 * uninitialised return register as the store's success flag. */
int8_t rt_array_set(SplArray* a, int64_t idx, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    if (idx < 0) idx = array->len + idx;
    if (idx < 0 || idx >= array->len) return 0;
    if (array->flags & RT_CORE_ARRAY_FLAG_BYTES) {
        ((uint8_t*)array->data)[idx] = (uint8_t)(rt_core_numeric_arg(val) & 0xff);
    } else {
        ((int64_t*)array->data)[idx] = val;
    }
    return 1;
}

int8_t rt_array_set_text(SplArray* a, int64_t idx, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    return rt_array_set(a, idx, val);
}

int8_t rt_array_push(SplArray* a, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    if (!rt_core_array_reserve(a, array->len + 1)) return 0;
    if (array->flags & RT_CORE_ARRAY_FLAG_BYTES) {
        ((uint8_t*)array->data)[array->len++] = (uint8_t)(rt_core_numeric_arg(val) & 0xff);
    } else {
        ((int64_t*)array->data)[array->len++] = val;
    }
    return 1;
}

/* Receiver-dispatched push parity with the hosted RuntimeValue provider.
 * Arrays mutate in place and return their receiver; text remains immutable and
 * returns the concatenated value. Other receiver kinds fail closed to nil. */
int64_t rt_push(int64_t receiver, int64_t value) {
    SplArray* array = (SplArray*)(uintptr_t)receiver;
    if (rt_core_array_ptr(array)) {
        if (!rt_array_push(array, value)) return rt_core_nil();
        return receiver;
    }
    if (rt_core_as_string(receiver)) return rt_string_concat(receiver, value);
    return rt_core_nil();
}

int8_t rt_array_clear(SplArray* a) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    array->len = 0;
    return 1;
}

int8_t rt_array_push_i64_raw(SplArray* a, int64_t val) {
    return rt_array_push(a, val);
}

/* Bulk element copy between two array handles: copies `count` slots from
 * src[src_off..] into dst[dst_off..]. Contract mirrors the seed runtime's
 * rt_array_write_span (compiler_rust/runtime value/collections.rs): returns
 * 0 for count <= 0, -1 on any out-of-bounds or invalid handle, else count.
 * Overlap-safe for dst == src (memmove). The memmove fast path requires the
 * FULL storage layout to match — BOTH the BYTES flag AND the U64_PACKED flag
 * (same pairwise flag-equality discipline as rt_core_array_eq above): a
 * packed slot holds a raw u64 while an unpacked non-bytes slot holds a
 * TAGGED value, so a bit copy between them silently corrupts. Any layout
 * mismatch takes the per-element path, which normalizes each element to a
 * raw u64 and re-encodes for the destination layout — the exact conversion
 * pattern the rt_typed_words_* accessors use (rt_value_as_u64 to read a
 * tagged slot, rt_core_value_u64_compact to store into one). */
int64_t rt_array_write_span(SplArray* dst, SplArray* src, int64_t dst_off,
                            int64_t src_off, int64_t count) {
    if (count <= 0) return 0;
    RtCoreArray* d = rt_core_array_ptr(dst);
    RtCoreArray* s = rt_core_array_ptr(src);
    if (!d || !s) return -1;
    /* Explicit count-vs-len checks first so `len - count` can never
     * underflow below the signed range (pathological huge counts). */
    if (dst_off < 0 || src_off < 0 || count > d->len || count > s->len ||
        dst_off > d->len - count || src_off > s->len - count) return -1;
    int d_bytes = (d->flags & RT_CORE_ARRAY_FLAG_BYTES) != 0;
    int s_bytes = (s->flags & RT_CORE_ARRAY_FLAG_BYTES) != 0;
    int d_u64 = (d->flags & RT_CORE_ARRAY_FLAG_U64_PACKED) != 0;
    int s_u64 = (s->flags & RT_CORE_ARRAY_FLAG_U64_PACKED) != 0;
    if (d_bytes == s_bytes && d_u64 == s_u64) {
        size_t esz = d_bytes ? sizeof(uint8_t) : sizeof(int64_t);
        memmove((uint8_t*)d->data + (size_t)dst_off * esz,
                (uint8_t*)s->data + (size_t)src_off * esz,
                (size_t)count * esz);
        return count;
    }
    /* Cross-layout copy: distinct layouts imply distinct arrays, so plain
     * forward order needs no overlap handling. */
    for (int64_t i = 0; i < count; i++) {
        int64_t slot = s_bytes ? (int64_t)((uint8_t*)s->data)[src_off + i]
                               : ((int64_t*)s->data)[src_off + i];
        int64_t raw = (s_bytes || s_u64) ? slot : rt_value_as_u64(slot);
        if (d_bytes) {
            ((uint8_t*)d->data)[dst_off + i] = (uint8_t)(raw & 0xff);
        } else {
            ((int64_t*)d->data)[dst_off + i] =
                d_u64 ? raw : rt_core_value_u64_compact(raw);
        }
    }
    return count;
}

int64_t rt_array_get_i64_raw(SplArray* a, int64_t index) {
    return rt_array_get(a, index);
}

SplArray* rt_array_concat(SplArray* a, SplArray* b) {
    RtCoreArray* left = rt_core_array_ptr(a);
    RtCoreArray* right = rt_core_array_ptr(b);
    if (!left || !right || left->len > INT64_MAX - right->len) return NULL;

    int64_t total = left->len + right->len;
    if (total > RT_CORE_ARRAY_MAX_CAP) return NULL;
    int left_bytes = (left->flags & RT_CORE_ARRAY_FLAG_BYTES) != 0;
    int right_bytes = (right->flags & RT_CORE_ARRAY_FLAG_BYTES) != 0;
    int left_u64 = (left->flags & RT_CORE_ARRAY_FLAG_U64_PACKED) != 0;
    int right_u64 = (right->flags & RT_CORE_ARRAY_FLAG_U64_PACKED) != 0;
    if (left_u64 != right_u64) return NULL;

    SplArray* result = left_bytes && right_bytes
        ? rt_byte_array_new((uint64_t)total)
        : (left_u64 && right_u64 ? rt_array_new_with_cap_u64(total) : rt_array_new(total));
    RtCoreArray* out = rt_core_array_ptr(result);
    if (!out) return NULL;

    if (left_bytes && right_bytes) {
        if (left->len > 0) memcpy(out->data, left->data, (size_t)left->len);
        if (right->len > 0) memcpy((uint8_t*)out->data + left->len, right->data, (size_t)right->len);
    } else if (left_u64 && right_u64) {
        if (left->len > 0) memcpy(out->data, left->data, (size_t)left->len * sizeof(uint64_t));
        if (right->len > 0) {
            memcpy((uint64_t*)out->data + left->len, right->data, (size_t)right->len * sizeof(uint64_t));
        }
    } else {
        int64_t* items = (int64_t*)out->data;
        for (int64_t i = 0; i < left->len; i++) {
            items[i] = left_bytes ? rt_value_int(((uint8_t*)left->data)[i]) : ((int64_t*)left->data)[i];
        }
        for (int64_t i = 0; i < right->len; i++) {
            items[left->len + i] =
                right_bytes ? rt_value_int(((uint8_t*)right->data)[i]) : ((int64_t*)right->data)[i];
        }
    }
    out->len = total;
    return result;
}

/* rt_array_copy: private shallow copy of an existing array's backing buffer,
 * matching simple_runtime::value::collections::rt_array_copy's semantics
 * ("allocates a new array of the same length, copies every element").
 * Needed on the core-c-bootstrap runtime lane because MIR lowering's
 * array-place-alias-copy fix (`var c = arr` -> rt_array_copy(vreg), commit
 * 8cccc7b70bc) has no C-runtime sibling: without this, the linker's
 * C-preferred symbol resolution (native_project/linker.rs) only has the Rust
 * implementation to route the call to, which expects a Rust-registered
 * RuntimeValue (via get_typed_ptr/is_registered_heap_ptr) and silently
 * returns a bogus sentinel for the plain RtCoreArray-backed SplArray handles
 * this lane's cranelift-compiled array ops (rt_array_new, rt_array_push,
 * rt_array_len, all defined in this file) actually produce -- corrupting
 * files.len() to 0 in test_runner_main.spl's "var files = all_files". */
SplArray* rt_array_copy(SplArray* a) {
    RtCoreArray* src = rt_core_array_ptr(a);
    if (!src) return a;
    int is_bytes = (src->flags & RT_CORE_ARRAY_FLAG_BYTES) != 0;
    int is_u64 = (src->flags & RT_CORE_ARRAY_FLAG_U64_PACKED) != 0;
    SplArray* result = is_bytes
        ? rt_byte_array_new((uint64_t)src->len)
        : (is_u64 ? rt_array_new_with_cap_u64(src->len) : rt_array_new(src->len));
    RtCoreArray* out = rt_core_array_ptr(result);
    if (!out) return result;
    if (src->len > 0) {
        size_t elem_size = is_bytes ? sizeof(uint8_t) : sizeof(int64_t);
        memcpy(out->data, src->data, (size_t)src->len * elem_size);
    }
    out->len = src->len;
    return result;
}

/* FR-COMPILER-012: array-repeat for `[value; count]` syntax in JIT.
 * Creates a new array with `count` copies of `value`. */
SplArray* rt_array_repeat(int64_t value, int64_t count) {
    int64_t n = count;
    if (n < 0) n = 0;
    SplArray* a = rt_core_array_new_fill(n, 0, 0);
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return a;
    array->len = n;
    if (n <= 0 || !array->data) {
        return a;
    }
    if (array->flags & RT_CORE_ARRAY_FLAG_BYTES) {
        memset(array->data, (int)(rt_core_numeric_arg(value) & 0xff), (size_t)n);
        return a;
    }
    int64_t* data = (int64_t*)array->data;
    data[0] = value;
    int64_t filled = 1;
    while (filled < n) {
        int64_t chunk = filled;
        if (chunk > n - filled) chunk = n - filled;
        memcpy(data + filled, data, (size_t)chunk * sizeof(int64_t));
        filled += chunk;
    }
    return a;
}

int64_t rt_array_data_ptr(SplArray* a) {
    RtCoreArray* array = rt_core_array_ptr(a);
    return array ? (int64_t)(uintptr_t)array->data : 0;
}

int64_t rt_array_data_ptr_text(SplArray* a) {
    return rt_array_data_ptr(a);
}

#if !defined(SIMPLE_RUNTIME_DYNLOAD_OWNER)
/* Hosted dynamic loading, per-lane fallback copy.
 *
 * runtime_dynload.c is the canonical owner (see
 * test/01_unit/compiler/backend/runtime_dynload_owner_source_spec.spl). It is
 * NOT in every bundle: runtime_compiler.spl drops it under native-all, and the
 * core-c lane (native_project/tools.rs) compiles runtime_native.c without it.
 * Those lanes need a definition here, so this copy exists — but it must never
 * co-exist with the owner in one bundle. runtime_compiler.spl defines
 * SIMPLE_RUNTIME_DYNLOAD_OWNER exactly when it pushes runtime_dynload, which
 * compiles this copy out and leaves exactly ONE definition per bundle.
 *
 * The bodies below are kept BYTE-IDENTICAL to runtime_dynload.c's (enforced by
 * the `same` marker in scripts/check/runtime_bundle_duplicate_symbols_baseline.txt).
 * Until 2026-08-05 they were NOT: this copy decoded its argument with
 * rt_core_string_to_cstring, which returns NULL for anything that is not a
 * tagged heap RtCoreString. A raw char* (how a bootstrap string literal reaches
 * an extern) therefore made spl_dlopen return 0 — indistinguishable from a
 * missing library. Because the bundle links runtime_native.o BEFORE
 * runtime_dynload.o under -z muldefs, THIS weaker copy was the one that won.
 * rt_interp_cstr accepts both encodings and is a strict superset. */
int64_t spl_dlopen(int64_t path_value) {
    const char* path = rt_interp_cstr(path_value);
    if (!path) return 0;
#ifdef _WIN32
    return (int64_t)(intptr_t)LoadLibraryA(path);
#else
    return (int64_t)(intptr_t)dlopen(path, RTLD_NOW | RTLD_LOCAL);
#endif
}

int64_t spl_dlsym(int64_t handle, int64_t name_value) {
    const char* name = rt_interp_cstr(name_value);
    if (!handle || !name) return 0;
#ifdef _WIN32
    return (int64_t)(intptr_t)GetProcAddress((HMODULE)(intptr_t)handle, name);
#else
    return (int64_t)(intptr_t)dlsym((void*)(intptr_t)handle, name);
#endif
}

int64_t spl_dlclose(int64_t handle) {
    if (!handle) return -1;
#ifdef _WIN32
    return FreeLibrary((HMODULE)(intptr_t)handle) ? 0 : -1;
#else
    return (int64_t)dlclose((void*)(intptr_t)handle);
#endif
}
#endif /* !SIMPLE_RUNTIME_DYNLOAD_OWNER */

int64_t spl_wffi_call_i64(int64_t fptr, int64_t args_value, int64_t nargs) {
    typedef int64_t (*Fn0)(void);
    typedef int64_t (*Fn1)(int64_t);
    typedef int64_t (*Fn2)(int64_t, int64_t);
    typedef int64_t (*Fn3)(int64_t, int64_t, int64_t);
    typedef int64_t (*Fn4)(int64_t, int64_t, int64_t, int64_t);
    typedef int64_t (*Fn5)(int64_t, int64_t, int64_t, int64_t, int64_t);
    typedef int64_t (*Fn6)(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t);
    typedef int64_t (*Fn7)(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t);
    typedef int64_t (*Fn8)(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t);
    if (fptr == 0 || nargs < 0 || nargs > 8) return 0;
    RtCoreArray* args = rt_core_as_array(args_value);
    if (nargs > 0 && (!args || args->flags & RT_CORE_ARRAY_FLAG_BYTES || !args->data || nargs > args->len)) return 0;
    int64_t raw[8] = {0};
    for (int64_t i = 0; i < nargs; i++) raw[i] = rt_core_as_int(((int64_t*)args->data)[i]);
    switch (nargs) {
        case 0: return ((Fn0)(uintptr_t)fptr)();
        case 1: return ((Fn1)(uintptr_t)fptr)(raw[0]);
        case 2: return ((Fn2)(uintptr_t)fptr)(raw[0], raw[1]);
        case 3: return ((Fn3)(uintptr_t)fptr)(raw[0], raw[1], raw[2]);
        case 4: return ((Fn4)(uintptr_t)fptr)(raw[0], raw[1], raw[2], raw[3]);
        case 5: return ((Fn5)(uintptr_t)fptr)(raw[0], raw[1], raw[2], raw[3], raw[4]);
        case 6: return ((Fn6)(uintptr_t)fptr)(raw[0], raw[1], raw[2], raw[3], raw[4], raw[5]);
        case 7: return ((Fn7)(uintptr_t)fptr)(raw[0], raw[1], raw[2], raw[3], raw[4], raw[5], raw[6]);
        case 8: return ((Fn8)(uintptr_t)fptr)(raw[0], raw[1], raw[2], raw[3], raw[4], raw[5], raw[6], raw[7]);
        default: return 0;
    }
}

int64_t rt_array_header_ptr(SplArray* a) {
    RtCoreArray* array = rt_core_array_ptr(a);
    return array ? (int64_t)(uintptr_t)array : 0;
}

int8_t rt_array_set_len_known(int64_t header_ptr, int64_t len) {
    RtCoreArray* array = rt_core_as_array(header_ptr);
    if (!array || len < 0 || len > array->cap) return 0;
    array->len = len;
    return 1;
}

int8_t rt_array_set_len_known_text(int64_t header_ptr, int64_t len) {
    return rt_array_set_len_known(header_ptr, len);
}

static int8_t rt_core_array_reserve(SplArray* a, int64_t min_cap) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    if (array->cap >= min_cap) return 1;
    int64_t new_cap = array->cap > 0 ? array->cap : 4;
    while (new_cap < min_cap) {
        if (new_cap > INT64_MAX / 2) return 0;
        new_cap *= 2;
    }
    size_t elem_size = (array->flags & RT_CORE_ARRAY_FLAG_BYTES) ? sizeof(uint8_t) : sizeof(int64_t);
    void* data = realloc(array->data, (size_t)new_cap * elem_size);
    if (!data) {
        array->len = 0;
        array->cap = 0;
        return 0;
    }
    array->data = data;
    array->cap = new_cap;
    return 1;
}

int64_t rt_bytes_u8_at(SplArray* a, int64_t idx) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    if (idx < 0) idx = array->len + idx;
    if (idx < 0 || idx >= array->len) return 0;
    if (array->flags & RT_CORE_ARRAY_FLAG_BYTES) {
        return (int64_t)((uint8_t*)array->data)[idx];
    }
    return rt_core_as_int(((int64_t*)array->data)[idx]) & 0xff;
}

int64_t rt_bytes_u32_le_at(SplArray* a, int64_t idx) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    if (idx < 0) idx = array->len + idx;
    if (idx < 0 || idx + 4 > array->len) return 0;
    uint64_t v = 0;
    for (int shift = 0; shift < 4; shift++) {
        uint64_t byte = (array->flags & RT_CORE_ARRAY_FLAG_BYTES)
            ? ((uint8_t*)array->data)[idx + shift]
            : (uint64_t)(rt_core_as_int(((int64_t*)array->data)[idx + shift]) & 0xff);
        v |= byte << (shift * 8);
    }
    return (int64_t)v;
}

int64_t rt_bytes_u64_le_at(SplArray* a, int64_t idx) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    if (idx < 0) idx = array->len + idx;
    if (idx < 0 || idx + 8 > array->len) return 0;
    uint64_t v = 0;
    for (int shift = 0; shift < 8; shift++) {
        uint64_t byte = (array->flags & RT_CORE_ARRAY_FLAG_BYTES)
            ? ((uint8_t*)array->data)[idx + shift]
            : (uint64_t)(rt_core_as_int(((int64_t*)array->data)[idx + shift]) & 0xff);
        v |= byte << (shift * 8);
    }
    return (int64_t)v;
}

int8_t rt_bytes_u8_set(SplArray* a, int64_t idx, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    val &= 0xff;
    if (idx < 0) idx = array->len + idx;
    if (idx < 0 || idx >= array->len) return 0;
    if (array->flags & RT_CORE_ARRAY_FLAG_BYTES) {
        ((uint8_t*)array->data)[idx] = (uint8_t)val;
    } else {
        ((int64_t*)array->data)[idx] = val << 3;
    }
    return 1;
}

int8_t rt_typed_bytes_u8_push(SplArray* a, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    val = val & 0xff;
    if (!rt_core_array_reserve(a, array->len + 1)) return 0;
    if (array->flags & RT_CORE_ARRAY_FLAG_BYTES) {
        ((uint8_t*)array->data)[array->len++] = (uint8_t)val;
    } else {
        ((int64_t*)array->data)[array->len++] = val << 3;
    }
    return 1;
}

int64_t rt_typed_bytes_u8_unchecked(SplArray* a, int64_t idx) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    if (array->flags & RT_CORE_ARRAY_FLAG_BYTES) {
        return (int64_t)((uint8_t*)array->data)[idx];
    }
    return rt_core_as_int(((int64_t*)array->data)[idx]) & 0xff;
}

int64_t rt_typed_bytes_u32_le_at(SplArray* a, int64_t idx) {
    return rt_bytes_u32_le_at(a, idx);
}

int64_t rt_typed_bytes_u64_le_at(SplArray* a, int64_t idx) {
    return rt_bytes_u64_le_at(a, idx);
}

int64_t rt_typed_bytes_u64_le_unchecked(SplArray* a, int64_t idx) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    uint64_t v = 0;
    for (int shift = 0; shift < 8; shift++) {
        uint64_t byte = (array->flags & RT_CORE_ARRAY_FLAG_BYTES)
            ? ((uint8_t*)array->data)[idx + shift]
            : (uint64_t)(rt_core_as_int(((int64_t*)array->data)[idx + shift]) & 0xff);
        v |= byte << (shift * 8);
    }
    return (int64_t)v;
}

int8_t rt_typed_bytes_u32_le_set(SplArray* a, int64_t idx, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    if (idx < 0 || idx + 4 > array->len) return 0;
    uint32_t v = (uint32_t)val;
    for (int shift = 0; shift < 4; shift++) {
        int64_t byte = (int64_t)((v >> (shift * 8)) & 0xff);
        if (array->flags & RT_CORE_ARRAY_FLAG_BYTES) {
            ((uint8_t*)array->data)[idx + shift] = (uint8_t)byte;
        } else {
            ((int64_t*)array->data)[idx + shift] = rt_value_int(byte);
        }
    }
    return 1;
}

int8_t rt_typed_bytes_u64_le_set(SplArray* a, int64_t idx, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    if (idx < 0 || idx + 8 > array->len) return 0;
    uint64_t v = (uint64_t)val;
    for (int shift = 0; shift < 8; shift++) {
        int64_t byte = (int64_t)((v >> (shift * 8)) & 0xff);
        if (array->flags & RT_CORE_ARRAY_FLAG_BYTES) {
            ((uint8_t*)array->data)[idx + shift] = (uint8_t)byte;
        } else {
            ((int64_t*)array->data)[idx + shift] = rt_value_int(byte);
        }
    }
    return 1;
}

int64_t rt_typed_words_u32_at(SplArray* a, int64_t idx) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    if (idx < 0) idx = array->len + idx;
    if (idx < 0 || idx >= array->len) return 0;
    int64_t value = ((int64_t*)array->data)[idx];
    if (!(array->flags & RT_CORE_ARRAY_FLAG_U64_PACKED)) value = rt_core_numeric_arg(value);
    return value & 0xffffffffLL;
}

int8_t rt_typed_words_u32_push(SplArray* a, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    if (!rt_core_array_reserve(a, array->len + 1)) return 0;
    val &= 0xffffffffLL;
    ((int64_t*)array->data)[array->len++] =
        (array->flags & RT_CORE_ARRAY_FLAG_U64_PACKED) ? val : rt_value_int(val);
    return 1;
}

int8_t rt_typed_words_u32_set(SplArray* a, int64_t idx, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    if (idx < 0) idx = array->len + idx;
    if (idx < 0 || idx >= array->len) return 0;
    val &= 0xffffffffLL;
    ((int64_t*)array->data)[idx] =
        (array->flags & RT_CORE_ARRAY_FLAG_U64_PACKED) ? val : rt_value_int(val);
    return 1;
}

int64_t rt_typed_words_u64_at(SplArray* a, int64_t idx) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    if (idx < 0) idx = array->len + idx;
    if (idx < 0 || idx >= array->len) return 0;
    int64_t value = ((int64_t*)array->data)[idx];
    return (array->flags & RT_CORE_ARRAY_FLAG_U64_PACKED) ? value : rt_value_as_u64(value);
}

int8_t rt_typed_words_u64_push(SplArray* a, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    if (!rt_core_array_reserve(a, array->len + 1)) return 0;
    ((int64_t*)array->data)[array->len++] =
        (array->flags & RT_CORE_ARRAY_FLAG_U64_PACKED) ? val : rt_core_value_u64_compact(val);
    return 1;
}

int8_t rt_typed_words_u64_set(SplArray* a, int64_t idx, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    if (idx < 0) idx = array->len + idx;
    if (idx < 0 || idx >= array->len) return 0;
    ((int64_t*)array->data)[idx] =
        (array->flags & RT_CORE_ARRAY_FLAG_U64_PACKED) ? val : rt_core_value_u64_compact(val);
    return 1;
}

int64_t rt_typed_words_u64_raw_data_at(int64_t data_ptr, int64_t idx) {
    if (data_ptr == 0 || idx < 0) return 0;
    return ((int64_t*)(uintptr_t)data_ptr)[idx];
}

int8_t rt_typed_words_u64_store_known_data_at(
    int64_t header_ptr,
    int64_t data_ptr,
    int64_t idx,
    int64_t val) {
    RtCoreArray* array = rt_core_as_array(header_ptr);
    if (!array || data_ptr == 0 || idx < 0 || idx >= array->cap) return 0;
    ((int64_t*)(uintptr_t)data_ptr)[idx] =
        (array->flags & RT_CORE_ARRAY_FLAG_U64_PACKED) ? val : rt_core_value_u64_compact(val);
    return 1;
}

int64_t rt_tuple_new(int64_t len) {
    SplArray* tuple = rt_array_new(len);
    if (!tuple) return rt_core_nil();
    RtCoreArray* array = rt_core_array_ptr(tuple);
    if (!array) return rt_core_nil();
    array->len = len < 0 ? 0 : len;
    /* Mark so rt_to_string can format this as "(a, b)" instead of the plain
     * array's "[a, b]" -- see RT_CORE_ARRAY_FLAG_TUPLE above. */
    array->flags |= RT_CORE_ARRAY_FLAG_TUPLE;
    return (int64_t)(uintptr_t)tuple;
}

int8_t rt_tuple_set(int64_t tuple, int64_t idx, int64_t value) {
    RtCoreArray* array = rt_core_as_array(tuple);
    if (!array) return 0;
    if (idx < 0 || idx >= array->len) return 0;
    ((int64_t*)array->data)[idx] = value;
    return 1;
}

int64_t rt_tuple_get(int64_t tuple, int64_t idx) {
    RtCoreArray* array = rt_core_as_array(tuple);
    if (!array) return rt_core_nil();
    if (idx < 0 || idx >= array->len) return rt_core_nil();
    return ((int64_t*)array->data)[idx];
}

int64_t rt_tuple_len(int64_t tuple) {
    RtCoreArray* array = rt_core_as_array(tuple);
    return array ? array->len : -1;
}

/* Enum-eq bug (enumtext lane, filed bug #2): `==` on an enum value has no
 * dedicated MIR routing (falls straight through to a raw integer/pointer
 * compare of the two tagged handles -- that generic Binary(Eq) dispatch
 * lives in expr_dispatch.spl, owned by a different lane this round) and
 * there is no rt_enum_eq. Before this fix, rt_enum_new unconditionally
 * malloc'd a FRESH RtCoreEnum for every construction -- including
 * payload-less (Unit) variants -- so two independently-constructed
 * instances of the exact same variant (`E.B == E.B`) always compared
 * unequal even though they are structurally identical.
 *
 * Fix: intern by (enum_id, discriminant, payload). A Unit variant's payload
 * is always the constant 0 (see lower_enum_lit/lower_enum_construct_named
 * in switch_operators_calls.spl), so two Unit constructions of the same
 * variant always hit the same cache slot and return the SAME pointer --
 * making the existing raw pointer-compare `==` correctly report equal.
 * As a side effect this also correctly interns SCALAR payloads with equal
 * bit patterns (e.g. `Some(3) == Some(3)`), matching value semantics for
 * i64/bool payloads. A POINTER-typed payload (text/struct) only interns
 * when the exact same pointer is reused; it never interns two
 * differently-allocated-but-equal-content payloads, so this is strictly
 * additive -- it never turns a previously-correct "unequal" result into an
 * incorrect one, it only fixes previously-wrong "unequal" results for
 * payload-less/equal-scalar-payload variants. RtCoreEnum has no in-place
 * mutation API (only rt_enum_discriminant/rt_enum_payload readers exist),
 * so sharing one allocation across equal constructions is safe.
 *
 * Custom enum call sites pass a stable qualified-type ID; Result and Option
 * retain their reserved IDs 0 and 1. Structural equality checks the ID too,
 * so distinct enum types cannot compare equal merely because their variant
 * ordinal and payload match. */
#define RT_ENUM_INTERN_MAX 4096
typedef struct RtEnumInternEntry {
    int32_t enum_id;
    int32_t discriminant;
    int64_t payload;
    int64_t value;
} RtEnumInternEntry;
static RtEnumInternEntry rt_enum_intern_table[RT_ENUM_INTERN_MAX];
static int rt_enum_intern_count = 0;

int64_t rt_enum_new(int32_t enum_id, int32_t discriminant, int64_t payload) {
    const int transient = rt_core_transient_scope_for_new_object() != 0;
    if (!transient) {
        for (int i = 0; i < rt_enum_intern_count; i++) {
            if (rt_enum_intern_table[i].enum_id == enum_id &&
                rt_enum_intern_table[i].discriminant == discriminant &&
                rt_enum_intern_table[i].payload == payload) {
                return rt_enum_intern_table[i].value;
            }
        }
    }
    RtCoreEnum* value = (RtCoreEnum*)calloc(1, sizeof(RtCoreEnum));
    if (!value) return rt_core_nil();
    value->kind = RT_VALUE_HEAP_ENUM;
    value->enum_id = (uint32_t)enum_id;
    value->discriminant = (uint32_t)discriminant;
    value->payload = payload;
    if (!rt_core_register_enum(value)) {
        free(value);
        return rt_core_nil();
    }
    int64_t tagged = (int64_t)(((uint64_t)(uintptr_t)value) | RT_VALUE_TAG_HEAP);
    if (!transient && rt_enum_intern_count < RT_ENUM_INTERN_MAX) {
        rt_enum_intern_table[rt_enum_intern_count].enum_id = enum_id;
        rt_enum_intern_table[rt_enum_intern_count].discriminant = discriminant;
        rt_enum_intern_table[rt_enum_intern_count].payload = payload;
        rt_enum_intern_table[rt_enum_intern_count].value = tagged;
        rt_enum_intern_count++;
    }
    return tagged;
}

int64_t rt_enum_discriminant(int64_t value) {
    RtCoreEnum* e = rt_core_as_enum(value);
    return e ? (int64_t)e->discriminant : -1;
}

int64_t rt_enum_id(int64_t value) {
    RtCoreEnum* e = rt_core_as_enum(value);
    return e ? (int64_t)e->enum_id : -1;
}

int8_t rt_enum_check_discriminant(int64_t value, int64_t expected) {
    RtCoreEnum* e = rt_core_as_enum(value);
    return e && (int64_t)e->discriminant == expected;
}

int64_t rt_enum_payload(int64_t value) {
    RtCoreEnum* e = rt_core_as_enum(value);
    return e ? e->payload : rt_core_nil();
}

/* Array `at`: bounds-checked element access with an Option (`T?`) result.
 *
 * The native lane previously had NO array `at` at all -- the LLVM codegen
 * mapped the method name `at` straight to the string-only `rt_string_char_at`
 * with no receiver test, so `arr.at(i)` took the TEXT path and read as absent
 * for EVERY index, in-range hits included, with no error and no crash. See
 * doc/08_tracking/bug/array_at_native_llvm_lane_2026-08-01.md.
 *
 * Deliberately NOT built on rt_array_get, for two independent reasons:
 *
 *  1. rt_array_get NORMALIZES the index Python-style (`if (idx < 0) idx =
 *     len + idx`), so `at(-1)` would silently wrap to the last element instead
 *     of reporting absence. Bounds here are checked SIGNED and UNNORMALIZED,
 *     matching the tree-walking interpreter's array `at` arm (f18c5963132) and
 *     the Rust runtime's rt_array_at: present iff `0 <= index < len`.
 *
 *  2. rt_array_get reports a miss by returning the raw nil sentinel 3
 *     (RT_NIL). Array elements on this lane are RAW i64 words, so an element
 *     whose value happens to be 3 is indistinguishable from absence BY
 *     CONSTRUCTION. `xs.at(3)` on `[0,1,2,3,4]` is exactly that case. A
 *     flat/raw optional therefore cannot express this operation safely.
 *
 * So the result is a CANONICAL BOXED Option: enum_id 1 with ordinal Some=0 /
 * None=1, the representation rt_is_none() above already recognises. Boxing
 * removes the collision entirely -- absence is a distinct heap enum object,
 * never the payload word -- which is the same conclusion the JIT lane reached
 * in ceee960ca8e.
 *
 * The payload is the RAW element word, matching what `xs[i]` (rt_array_get)
 * yields on this lane, so `.at()` and `[i]` cannot silently disagree.
 */
int64_t rt_array_at(SplArray* a, int64_t idx) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return rt_enum_new(1, 1, rt_core_nil());
    if (idx < 0 || idx >= array->len) return rt_enum_new(1, 1, rt_core_nil());
    int64_t elem;
    if (array->flags & RT_CORE_ARRAY_FLAG_BYTES) {
        elem = (int64_t)((uint8_t*)array->data)[idx];
    } else {
        elem = ((int64_t*)array->data)[idx];
    }
    return rt_enum_new(1, 0, elem);
}

/* Receiver-dispatching `at`.
 *
 * The codegen sites dispatch purely on the method NAME and do not all have a
 * reliable static receiver type available, so the receiver test is done here
 * at runtime -- the same shape as the Cranelift/JIT `rt_at` added in
 * ceee960ca8e, so the two backends cannot answer differently for one source.
 *
 * Text behaviour is intentionally unchanged: `text.at(i)` still yields a raw
 * single-character string, NOT an Option. Only the array receiver -- which
 * previously had no implementation at all on this lane -- gains the Option.
 */
int64_t rt_at(int64_t receiver, int64_t index) {
    if (rt_core_as_array(receiver)) {
        return rt_array_at((SplArray*)(uintptr_t)receiver, index);
    }
    return rt_string_char_at(receiver, index);
}

int64_t rt_closure_new(int64_t func_ptr, int64_t capture_count) {
    if (!func_ptr || capture_count < 0) return rt_core_nil();
    size_t count = (size_t)capture_count;
    if (count > (SIZE_MAX - sizeof(RtCoreClosure)) / sizeof(int64_t)) return rt_core_nil();
    RtCoreClosure* closure =
        (RtCoreClosure*)calloc(1, sizeof(RtCoreClosure) + count * sizeof(int64_t));
    if (!closure) return rt_core_nil();
    closure->kind = RT_VALUE_HEAP_CLOSURE;
    closure->func_ptr = func_ptr;
    closure->capture_count = capture_count;
    if (!rt_core_register_closure(closure)) {
        free(closure);
        return rt_core_nil();
    }
    return (int64_t)(((uint64_t)(uintptr_t)closure) | RT_VALUE_TAG_HEAP);
}

int64_t rt_closure_set_capture(int64_t closure_value, int64_t index, int64_t value) {
    RtCoreClosure* closure = rt_core_as_closure(closure_value);
    if (!closure || index < 0 || index >= closure->capture_count) return 0;
    closure->captures[index] = value;
    return 1;
}

int64_t rt_closure_get_capture(int64_t closure_value, int64_t index) {
    RtCoreClosure* closure = rt_core_as_closure(closure_value);
    if (!closure || index < 0 || index >= closure->capture_count) return rt_core_nil();
    return closure->captures[index];
}

int64_t rt_closure_func_ptr(int64_t closure_value) {
    RtCoreClosure* closure = rt_core_as_closure(closure_value);
    return closure ? closure->func_ptr : 0;
}

/* Array collection ops that invoke a closure per element.
 *
 * The LLVM backend maps `("Array"|"array", "map"|"each"|"for_each"|
 * "reduce"|"fold")` to rt_array_map / rt_array_each / rt_array_reduce
 * (codegen/llvm/functions.rs) and emits `receiver + args` verbatim, so the
 * call shapes are exactly the ones below. Before these existed, `arr.map(f)`
 * under the LLVM backend failed at LINK time with `undefined reference to
 * 'rt_array_map'` -- neither the Rust runtime archive nor this one defined
 * the symbol.
 *
 * Closure ABI: identical to the Rust runtime's rt_array_filter/rt_array_find
 * and to what MIR lowering emits for a general indirect call
 * (50.mir/_MirLoweringExpr/switch_operators_calls.spl): the lifted target
 * takes the closure handle first so it can reach its captures, then the
 * element(s). A zero func_ptr means the value is not a registered closure;
 * these bail rather than calling through an unvalidated address.
 *
 * Iteration is by INDEX, re-reading the length each step: the closure is
 * arbitrary user code and may push to or clear the receiver, which would
 * invalidate a data pointer cached up front. rt_array_get re-reads the header
 * and honours the BYTES flag.
 */
typedef int64_t (*RtArrayElemFn)(int64_t, int64_t);
typedef int64_t (*RtArrayFoldFn)(int64_t, int64_t, int64_t);

int64_t rt_array_map(SplArray* array, int64_t closure_value) {
    SplArray* result = rt_array_new(rt_array_len(array));
    if (!result) return rt_core_nil();
    int64_t func_ptr = rt_closure_func_ptr(closure_value);
    if (!func_ptr) return (int64_t)(uintptr_t)result;
    RtArrayElemFn func = (RtArrayElemFn)(uintptr_t)func_ptr;
    for (int64_t i = 0; i < rt_array_len(array); i++) {
        rt_array_push(result, func(closure_value, rt_array_get(array, i)));
    }
    return (int64_t)(uintptr_t)result;
}

/* Returns the RECEIVER so `arr.each(f)` is chainable and never yields nil --
 * the call site is typed as returning i64 unconditionally, so a nil there
 * would be indistinguishable from failure. */
int64_t rt_array_each(SplArray* array, int64_t closure_value) {
    int64_t receiver = (int64_t)(uintptr_t)array;
    int64_t func_ptr = rt_closure_func_ptr(closure_value);
    if (!func_ptr) return receiver;
    RtArrayElemFn func = (RtArrayElemFn)(uintptr_t)func_ptr;
    for (int64_t i = 0; i < rt_array_len(array); i++) {
        func(closure_value, rt_array_get(array, i));
    }
    return receiver;
}

/* Left fold. `init` comes FIRST, matching the interpreter's `reduce(init,
 * func)` (interpreter_method/collections.rs) which invokes the function as
 * `(acc, item)` (interpreter_helpers/collections.rs). Reversing either order
 * would be a silently wrong answer for any non-commutative combiner, so both
 * are pinned to the interpreter rather than guessed. */
int64_t rt_array_reduce(SplArray* array, int64_t init, int64_t closure_value) {
    int64_t func_ptr = rt_closure_func_ptr(closure_value);
    if (!func_ptr) return init;
    RtArrayFoldFn func = (RtArrayFoldFn)(uintptr_t)func_ptr;
    int64_t acc = init;
    for (int64_t i = 0; i < rt_array_len(array); i++) {
        acc = func(closure_value, acc, rt_array_get(array, i));
    }
    return acc;
}

/* Truthiness, mirroring the Rust runtime's RuntimeValue::truthy()
 * (runtime/src/value/core.rs) branch for branch. The two runtimes MUST agree
 * on how a predicate's RESULT is judged: a divergence here is not a link error
 * but a silently different answer, visible only on whichever runtime a given
 * link happens to pull in.
 *
 * The float test comes FIRST, exactly as it does in Rust: a heap-boxed 0.0
 * carries RT_VALUE_TAG_HEAP, so judged by tag alone it would be "truthy
 * because the pointer exists". rt_core_is_float covers both the heap-boxed
 * form and the legacy inline RT_VALUE_TAG_FLOAT form, so both of Rust's float
 * arms are subsumed by the one test. */
static inline int rt_core_value_truthy(int64_t value) {
    if (rt_core_is_float(value)) return rt_core_as_float(value) != 0.0;
    switch (((uint64_t)value) & RT_VALUE_TAG_MASK) {
    case RT_VALUE_TAG_INT:
        return rt_core_as_int(value) != 0;
    case RT_VALUE_TAG_SPECIAL:
        return rt_core_special_payload(value) == RT_VALUE_SPECIAL_TRUE;
    case RT_VALUE_TAG_HEAP:
        return (((uint64_t)value) & ~RT_VALUE_TAG_MASK) != 0;
    default:
        return 0;
    }
}

/* Predicate-driven collection ops.
 *
 * Until now this runtime defined NONE of these six while the Rust runtime
 * defined all six, so the two runtimes were not at parity: whether
 * `arr.filter(f)` linked at all depended purely on which runtime a given link
 * pulled in. Measured against the built objects with a true-positive control
 * (rt_array_map / rt_array_each / rt_array_reduce / rt_array_get present,
 * these six absent) and confirmed at source level across every src/runtime
 * *.c, since archive-absence alone is not proof.
 *
 * Semantics are pinned to the INTERPRETER (interpreter_helpers/collections.rs
 * eval_array_filter / eval_array_find / eval_array_any / eval_array_all), not
 * guessed, and mirror the Rust runtime (runtime/src/value/collections.rs):
 *
 *   filter -> NEW array of the elements whose predicate result is truthy
 *   find   -> the FIRST element whose predicate result is truthy, else nil
 *   any    -> 1 on the FIRST truthy result (short-circuit); empty -> 0
 *   all    -> 0 on the FIRST falsy result (short-circuit); empty -> 1
 *
 * rt_array_any / rt_array_all take the predicate as a REAL operand. The Rust
 * runtime used to declare them as (array) only and forward to the _truthy
 * form, so the predicate operand was accepted by the ABI and then DISCARDED --
 * `[1,2,3].all(x => x > 10)` answered true and the predicate was never invoked
 * (fixed in f835ee71522). This runtime is written at the correct arity from
 * the start so that divergence is not reintroduced here.
 *
 * The zero-predicate spellings are SEPARATE symbols, not defaulted arguments:
 * `arr.all_truthy()` lowers to rt_array_all_truthy(array) through its own MIR
 * arm (mir/lower/lowering_expr_method.rs). A defaulted closure operand could
 * not be told apart from a real one, so the split is deliberate.
 *
 * A zero func_ptr means the operand is not a registered closure; like the Rust
 * runtime these degrade to element truthiness rather than calling through an
 * unvalidated address.
 *
 * Iteration is by INDEX, re-reading the length each step, for the same reason
 * rt_array_map does it: the predicate is arbitrary user code and may push to
 * or clear the receiver. */
int64_t rt_array_filter(SplArray* array, int64_t closure_value) {
    if (!rt_core_array_ptr(array)) return rt_core_nil();
    SplArray* result = rt_array_new(0);
    if (!result) return rt_core_nil();
    int64_t func_ptr = rt_closure_func_ptr(closure_value);
    if (!func_ptr) return (int64_t)(uintptr_t)result;
    RtArrayElemFn func = (RtArrayElemFn)(uintptr_t)func_ptr;
    for (int64_t i = 0; i < rt_array_len(array); i++) {
        int64_t item = rt_array_get(array, i);
        if (rt_core_value_truthy(func(closure_value, item))) {
            rt_array_push(result, item);
        }
    }
    return (int64_t)(uintptr_t)result;
}

int64_t rt_array_find(SplArray* array, int64_t closure_value) {
    if (!rt_core_array_ptr(array)) return rt_core_nil();
    int64_t func_ptr = rt_closure_func_ptr(closure_value);
    if (!func_ptr) return rt_core_nil();
    RtArrayElemFn func = (RtArrayElemFn)(uintptr_t)func_ptr;
    for (int64_t i = 0; i < rt_array_len(array); i++) {
        int64_t item = rt_array_get(array, i);
        if (rt_core_value_truthy(func(closure_value, item))) return item;
    }
    return rt_core_nil();
}

/* Non-array receiver answers 0 for BOTH _truthy forms, matching the Rust
 * as_typed_ptr! bail-out default. Note this is deliberately NOT the vacuous
 * `true` an empty loop would produce for all_truthy: "not an array" and "an
 * array all of whose elements are truthy" must not share an answer. */
int64_t rt_array_all_truthy(SplArray* array) {
    if (!rt_core_array_ptr(array)) return 0;
    for (int64_t i = 0; i < rt_array_len(array); i++) {
        if (!rt_core_value_truthy(rt_array_get(array, i))) return 0;
    }
    return 1;
}

int64_t rt_array_any_truthy(SplArray* array) {
    if (!rt_core_array_ptr(array)) return 0;
    for (int64_t i = 0; i < rt_array_len(array); i++) {
        if (rt_core_value_truthy(rt_array_get(array, i))) return 1;
    }
    return 0;
}

int64_t rt_array_all(SplArray* array, int64_t closure_value) {
    if (!rt_core_array_ptr(array)) return 0;
    int64_t func_ptr = rt_closure_func_ptr(closure_value);
    if (!func_ptr) return rt_array_all_truthy(array);
    RtArrayElemFn func = (RtArrayElemFn)(uintptr_t)func_ptr;
    for (int64_t i = 0; i < rt_array_len(array); i++) {
        if (!rt_core_value_truthy(func(closure_value, rt_array_get(array, i)))) return 0;
    }
    return 1;
}

int64_t rt_array_any(SplArray* array, int64_t closure_value) {
    if (!rt_core_array_ptr(array)) return 0;
    int64_t func_ptr = rt_closure_func_ptr(closure_value);
    if (!func_ptr) return rt_array_any_truthy(array);
    RtArrayElemFn func = (RtArrayElemFn)(uintptr_t)func_ptr;
    for (int64_t i = 0; i < rt_array_len(array); i++) {
        if (rt_core_value_truthy(func(closure_value, rt_array_get(array, i)))) return 1;
    }
    return 0;
}

/* ---------------------------------------------------------------------------
 * Receiver-polymorphic collection entry points, at parity with the Rust
 * runtime's rt_find / rt_map / rt_index_of.
 *
 * Every symbol below is implemented rather than left to fail at link ONLY
 * because its emitters were first shown to pass their operands verbatim: the
 * LLVM sites build `receiver + args` with get_vreg + coerce_value_to_type
 * (codegen/llvm/emitter.rs, codegen/llvm/functions.rs) and the Cranelift sites
 * do the same (codegen/instr/calls.rs, codegen/instr/closures_structs.rs). The
 * rt_par_map / rt_par_filter / rt_par_for_each / rt_par_reduce family is
 * DELIBERATELY still absent from this file: those emitters drop operands
 * (2 passed against 4 declared, 3 against 5), and an emitter that discards
 * operands must keep failing loudly rather than be handed a receiver.
 *
 * Signature divergence from the Rust runtime, recorded not reconciled: the
 * entry points here take a raw int64_t or an SplArray pointer where Rust takes
 * a tagged RuntimeValue, so the receiver test is rt_core_array_ptr rather than
 * the Rust as_typed_ptr heap-type check, and value equality is rt_native_eq
 * here against the Rust rt_value_eq. Behaviour is matched, the C types are not.
 * ------------------------------------------------------------------------- */

/* Index of the first element equal to `value`, or -1. Mirrors the Rust
 * rt_array_index_of, whose -1 doubles as the receiver-mismatch sentinel. This
 * had a runtime_sffi spec and a Rust definition but no definition here at all,
 * so `arr.index_of(v)` was an unresolved symbol on the C lane. */
int64_t rt_array_index_of(SplArray* array, int64_t value) {
    if (!rt_core_array_ptr(array)) return -1;
    for (int64_t i = 0; i < rt_array_len(array); i++) {
        if (rt_native_eq(rt_array_get(array, i), value)) return i;
    }
    return -1;
}

/* Receiver-polymorphic index_of: array first, then text. Dispatch is by trial
 * rather than a kind test because both callees are total and answer -1 on a
 * receiver mismatch, exactly as the Rust rt_index_of does. Both return a RAW
 * index, so there is no return-shape question here. */
int64_t rt_index_of(int64_t haystack, int64_t needle) {
    int64_t as_array = rt_array_index_of((SplArray*)(uintptr_t)haystack, needle);
    if (as_array >= 0) return as_array;
    return rt_string_find(haystack, needle);
}

/* Receiver-polymorphic find. See the Rust rt_find for the full rationale; the
 * one thing that must not be lost in a summary is that the RETURN SHAPE
 * DIFFERS BY RECEIVER and that this is the pre-existing contract, not a new
 * choice: an array receiver yields the tagged ELEMENT, a text receiver yields a
 * RAW index. hir/lower/expr/mod.rs types `find` as I64 only under `is_string`,
 * so the consumer already interprets the word by receiver type. Requiring a
 * callable closure for the array branch keeps every other argument shape on its
 * exact previous answer. */
int64_t rt_find(int64_t receiver, int64_t arg) {
    SplArray* arr = rt_core_array_ptr((SplArray*)(uintptr_t)receiver) ? (SplArray*)(uintptr_t)receiver : NULL;
    if (arr && rt_closure_func_ptr(arg)) {
        return rt_array_find(arr, arg);
    }
    return rt_string_find(receiver, arg);
}

/* Option::map. Absent from this file entirely until now, which is why the
 * type-blind `map` dispatch could not link on the C lane at all. Semantics are
 * pinned to the Rust rt_option_map (runtime/src/value/objects.rs): None/nil is
 * returned UNCHANGED with the closure never invoked, a null closure yields nil,
 * and otherwise the payload is passed to the closure and the result re-wrapped
 * in Some. Some is (enum_id 1, discriminant 0) and None is (1, 1) — the same
 * constants rt_array_at in this file already builds its Option with. */
int64_t rt_option_map(int64_t value, int64_t closure_value) {
    if (rt_is_none(value)) return value;
    int64_t payload = rt_enum_payload(value);
    int64_t func_ptr = rt_closure_func_ptr(closure_value);
    if (!func_ptr) return rt_core_nil();
    RtArrayElemFn func = (RtArrayElemFn)(uintptr_t)func_ptr;
    return rt_enum_new(1, 0, func(closure_value, payload));
}

/* Receiver-polymorphic map: arrays go to rt_array_map, everything else keeps
 * the exact rt_option_map result. Mirrors the Rust rt_map. The in-tree comment
 * that claimed rt_option_map "also works for arrays" was WRONG in the silent
 * direction — rt_enum_payload of an array is nil, so the closure ran exactly
 * ONCE, on a value never in the receiver, and the result came back Some-wrapped
 * with no error and exit 0. */
int64_t rt_map(int64_t receiver, int64_t closure_value) {
    SplArray* arr = rt_core_array_ptr((SplArray*)(uintptr_t)receiver) ? (SplArray*)(uintptr_t)receiver : NULL;
    if (arr) return rt_array_map(arr, closure_value);
    return rt_option_map(receiver, closure_value);
}

static int64_t rt_bdd_passed = 0;
static int64_t rt_bdd_failed = 0;
static int rt_bdd_current_failed = 0;

static void rt_bdd_print_text(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s || s->len == 0) return;
    fwrite(s->data, 1, (size_t)s->len, stdout);
}

void rt_bdd_describe_start_rv(int64_t name_rv) {
    rt_bdd_print_text(name_rv);
    fputc('\n', stdout);
}

void rt_bdd_describe_end(void) {
    printf("%lld examples, %lld failures\n",
           (long long)(rt_bdd_passed + rt_bdd_failed),
           (long long)rt_bdd_failed);
}

void rt_bdd_it_start_rv(int64_t name_rv) {
    rt_bdd_current_failed = 0;
    fputs("  ", stdout);
    rt_bdd_print_text(name_rv);
}

void rt_bdd_it_end(int64_t passed) {
    if (passed != 0 && !rt_bdd_current_failed) {
        rt_bdd_passed += 1;
        fputs(" pass\n", stdout);
    } else {
        rt_bdd_failed += 1;
        fputs(" fail\n", stdout);
    }
}

int64_t rt_bdd_has_failure(void) {
    return rt_bdd_current_failed ? 1 : 0;
}

void rt_bdd_expect_fail(int64_t msg_ptr, int64_t msg_len) {
    rt_bdd_current_failed = 1;
    if (msg_ptr != 0 && msg_len > 0) {
        fputs("\n    ", stdout);
        fwrite((const void*)(uintptr_t)msg_ptr, 1, (size_t)msg_len, stdout);
    }
}

void rt_bdd_expect_eq_rv(int64_t actual, int64_t expected) {
    RtCoreString* actual_string = rt_core_as_string(actual);
    RtCoreString* expected_string = rt_core_as_string(expected);
    RtCoreArray* actual_array = rt_core_as_registered_array(actual);
    RtCoreArray* expected_array = rt_core_as_registered_array(expected);
    int bool_equal =
        (actual == 1 && (expected == 16 || expected == (int64_t)rt_core_from_special(RT_VALUE_SPECIAL_TRUE))) ||
        (expected == 1 && (actual == 16 || actual == (int64_t)rt_core_from_special(RT_VALUE_SPECIAL_TRUE))) ||
        (actual == 0 && (expected == 24 || expected == (int64_t)rt_core_from_special(RT_VALUE_SPECIAL_FALSE))) ||
        (expected == 0 && (actual == 24 || actual == (int64_t)rt_core_from_special(RT_VALUE_SPECIAL_FALSE)));
    int64_t equal = (actual_string || expected_string || actual_array || expected_array)
        ? rt_native_eq(actual, expected)
        : (bool_equal || rt_core_numeric_arg(actual) == rt_core_numeric_arg(expected));
    if (equal != 1) {
        rt_bdd_current_failed = 1;
    }
}

void rt_bdd_expect_truthy_rv(int64_t value) {
    if (value == 0 || value == rt_core_nil()) {
        rt_bdd_current_failed = 1;
    }
}

void rt_bdd_expect_truthy(int64_t value) {
    rt_bdd_expect_truthy_rv(value);
}

int64_t rt_bdd_format_results(void) {
    rt_bdd_describe_end();
    return rt_bdd_failed;
}

void rt_bdd_clear_state(void) {
    rt_bdd_passed = 0;
    rt_bdd_failed = 0;
    rt_bdd_current_failed = 0;
}

int64_t rt_hash_text(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) return 0;
    uint64_t hash = 1469598103934665603ULL;
    for (uint64_t i = 0; i < s->len; i++) {
        hash ^= (uint8_t)s->data[i];
        hash *= 1099511628211ULL;
    }
    return (int64_t)hash;
}

int64_t rt_array_pop(SplArray* a) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array || array->len <= 0 || !array->data) return 3;
    int64_t idx = --array->len;
    if (array->flags & RT_CORE_ARRAY_FLAG_BYTES) {
        return (int64_t)((uint8_t*)array->data)[idx];
    }
    int64_t* data = (int64_t*)array->data;
    int64_t value = data[idx];
    data[idx] = 3;
    return value;
}

/* pop / clear: receiver-dispatched spellings of rt_array_pop/rt_array_clear.
 *
 * These had NO C definition anywhere (only the Rust runtime's
 * value/collections.rs), so the SimpleOS cross-link could not resolve them.
 * They are written HERE, beside their siblings, because RtCoreArray,
 * rt_core_as_array, rt_core_array_ptr and rt_refuse_non_text_receiver are all
 * file-local statics -- re-declaring RtCoreArray in a new translation unit is
 * exactly the layout-drift that links cleanly and corrupts silently.
 *
 * Dispatch shape follows rt_reverse above; the array bodies delegate to the
 * existing, already-correct rt_array_pop / rt_array_clear rather than
 * re-deriving element handling (default elements are 3-bit-tagged values,
 * FLAG_BYTES elements are raw bytes -- rt_array_pop already distinguishes
 * them).
 */
int64_t rt_pop(int64_t receiver) {
    SplArray* arr = rt_core_as_array(receiver) ? (SplArray*)(uintptr_t)receiver : NULL;
    if (arr) return rt_array_pop(arr);

    RtCoreString* s = rt_core_as_string(receiver);
    if (!s) rt_refuse_non_text_receiver("pop", receiver);
    /* Text pops the last CHARACTER, not the last byte: slicing a byte off a
     * multi-byte codepoint would emit invalid UTF-8.
     *
     * Text is PURE here while the array branch above mutates, and that
     * asymmetry is the spec, not an oversight. interpreter_method/string.rs:212
     * -- "Returns the LAST CHARACTER, and does not modify the string (strings
     * are immutable)" -- and interpreter_method/mod.rs:1870 applies pop's
     * receiver write-back only to `Value::Array`, never to text.
     *
     * Two further details copied from that arm rather than invented: an empty
     * text yields the EMPTY TEXT (unambiguous, since no real character is the
     * empty text), and the result is a bare text, never an Option -- text used
     * to be the only `pop` returning `Some(..)` and that was deliberately
     * removed as unreachable outside the interpreter. */
    if (s->len == 0) return rt_string_new((const uint8_t*)"", 0);
    uint64_t last = 0;
    for (uint64_t i = 0; i < s->len;) {
        uint64_t w = rt_utf8_width(s->data, i, s->len);
        last = i;
        i += w;
    }
    return rt_string_new((const uint8_t*)(s->data + last),
                         s->len - last);
}

/* clear returns the RECEIVER, which is why this is not an alias for
 * rt_array_clear. rt_array_clear's spec is &[I64] -> &[I8]; it returns 1 on
 * success. Returning that 1 from rt_clear would be decoded as a heap-tagged
 * pointer to address 0 (RT_VALUE_TAG_HEAP | 0) and segfault on first use --
 * a link-clean, corrupt-later bug. */
/* The DICT branch below is load-bearing for the Stage 3 self-host. The codegen
 * dispatch tables route `.clear()` here by NAME with no receiver type, so
 * `Dict.clear()` lands in this function; until 2026-08-17 there was no dict arm
 * and a dict receiver fell through to rt_refuse_non_text_receiver (and, before
 * that refusal existed, to a SILENT no-op). Either way
 * SymbolTable.reset_module() (src/compiler/20.hir/hir_types.spl:242) cleared
 * none of its eight dicts while its scalar resets (next_symbol_id = 0) still
 * took effect, so stale symbol NAMES from earlier modules pointed at ids the
 * next module had already reused. See the matching comment on rt_clear in
 * src/compiler_rust/runtime/src/value/collections.rs. rt_index_get, directly
 * below, is the three-way receiver-dispatch pattern this now follows. */
int8_t rt_dict_clear(int64_t dict);

int64_t rt_clear(int64_t receiver) {
    SplArray* arr = rt_core_as_array(receiver) ? (SplArray*)(uintptr_t)receiver : NULL;
    if (arr) {
        rt_array_clear(arr);
        return receiver;
    }
    if (rt_core_as_dict(receiver)) {
        rt_dict_clear(receiver);
        return receiver;
    }
    if (!rt_core_as_string(receiver)) rt_refuse_non_text_receiver("clear", receiver);
    return rt_string_new((const uint8_t*)"", 0);
}

int64_t rt_index_get(int64_t collection, int64_t idx) {
    RtCoreArray* a = rt_core_as_array(collection);
    if (a) {
        if ((idx & RT_VALUE_TAG_MASK) != RT_VALUE_TAG_INT) return rt_core_nil();
        return rt_array_get((SplArray*)a, idx >> 3);
    }
    if (rt_core_as_string(collection)) {
        if ((idx & RT_VALUE_TAG_MASK) != RT_VALUE_TAG_INT) return rt_core_nil();
        return rt_string_char_at(collection, idx >> 3);
    }
    RtCoreDict* d = rt_core_as_dict(collection);
    if (d) return rt_core_dict_lookup(d, idx);
    return 3;
}

int8_t rt_index_set(int64_t collection, int64_t idx, int64_t val) {
    RtCoreArray* a = rt_core_as_array(collection);
    if (a) {
        if ((idx & RT_VALUE_TAG_MASK) != RT_VALUE_TAG_INT) return 0;
        int64_t raw_idx = idx >> 3;
        if (raw_idx < 0) raw_idx += a->len;
        if (raw_idx < 0 || raw_idx >= a->len) return 0;
        rt_array_set((SplArray*)a, raw_idx, val);
        return 1;
    }
    RtCoreDict* d = rt_core_as_dict(collection);
    if (d) return (int8_t)rt_core_dict_put(d, idx, val);
    return 0;
}

/* ================================================================
 * Dict Operations (RtCore tagged-int64 hash table)
 * ================================================================ */

#define RT_CORE_DICT_INIT_CAP 8

/* Return the RtCoreDict if `value` is a registered dict, else NULL.
 * Registry membership is checked BEFORE ->kind is read, so a non-dict value
 * that merely carries the HEAP tag bits (another heap type, or a flat i64
 * payload aliasing the tag) resolves to "not a dict" instead of being
 * dereferenced. Structure mirrors rt_core_as_string. */
static RtCoreDict* rt_core_as_dict(int64_t value) {
    uintptr_t raw = (uintptr_t)value;
    if (raw < 4096) return NULL;
    if ((raw & RT_VALUE_TAG_MASK) != RT_VALUE_TAG_HEAP) return NULL;
    RtCoreDict* d = (RtCoreDict*)(raw & ~RT_VALUE_TAG_MASK);
    if (!rt_core_is_registered_dict(d)) return NULL;
    if (!d || d->kind != RT_VALUE_HEAP_DICT) return NULL;
    return d;
}

/* Canonicalize a key so that the raw-int form produced by `d[k] = v` (IndexSet,
 * unboxed) and the tagged form produced by `d.get(k)` (method path, rt_box_int)
 * collapse to one representation. String/heap keys are kept as-is and matched by
 * content via rt_native_eq. */
/* The 64 bits that IDENTIFY a float key, for both the heap-boxed form and the
 * legacy inline TAG_FLOAT form. -0.0 is folded to +0.0 so both zeros are one
 * key, matching IEEE `-0.0 == 0.0`; every other bit is preserved. */
static uint64_t rt_core_dict_float_bits(int64_t k) {
    double d = rt_core_as_float(k);
    if (d == 0.0) d = 0.0; /* fold -0.0 -> +0.0 so both zeros hash alike */
    uint64_t bits;
    memcpy(&bits, &d, sizeof(bits));
    return bits;
}

static int64_t rt_core_dict_canon_key(int64_t k) {
    if (rt_core_as_string(k)) return k;
    /* A heap-boxed float key is a fresh pointer per value, so two keys of the
     * same double would land in different buckets. That is a HASH problem, and
     * it is solved in rt_core_dict_hash below (which hashes the double's bits,
     * not the box address) plus rt_core_dict_key_eq (which compares those same
     * bits). The key itself is therefore stored VERBATIM.
     *
     * It used to be rewritten to the inline tagged form
     * `(bits & ~RT_VALUE_TAG_MASK) | RT_VALUE_TAG_FLOAT`, which ZEROES THE LOW
     * 3 MANTISSA BITS: every group of 8 adjacent doubles collapsed into one
     * key, so `d[1.0] = 1; d[1.0000000000000002] = 2` silently left a dict of
     * len 1 whose d[1.0] read back 2, and dict_keys() handed back a double the
     * caller never inserted. That contradicts RtCoreFloat's whole reason for
     * existing ("the full double is stored verbatim so container/Any floats
     * round-trip exactly"). See
     * src/runtime/test/rt_dict_float_key_exactness_selfcheck.c. */
    if (rt_core_is_float(k)) return k;
    RtCoreUInt* u = rt_core_as_heap_uint(k);
    if (u) {
        if (u->value <= (uint64_t)(INT64_MAX >> 3)) return rt_value_int((int64_t)u->value);
        return k;
    }
    if (rt_core_is_heap(k)) return k;
    return rt_value_int(rt_core_numeric_arg(k));
}

static uint64_t rt_core_dict_hash(int64_t k) {
    RtCoreString* s = rt_core_as_string(k);
    if (s) {
        uint64_t h = 1469598103934665603ULL; /* FNV-1a offset basis */
        for (uint64_t i = 0; i < s->len; i++) {
            h ^= (uint8_t)s->data[i];
            h *= 1099511628211ULL;
        }
        return h;
    }
    /* Float keys hash by VALUE, so two independent boxes of the same double --
     * and the legacy inline form of that same double -- share a bucket. */
    RtCoreUInt* u = rt_core_as_heap_uint(k);
    uint64_t x = u
        ? (u->value ^ UINT64_C(0x55494e545f553634))
        : (rt_core_is_float(k) ? rt_core_dict_float_bits(k) : (uint64_t)k);
    x ^= x >> 33;
    x *= 0xff51afd7ed558ccdULL;
    x ^= x >> 33;
    return x;
}

/* Key equality for the slot scan. rt_native_eq everywhere EXCEPT float keys,
 * which are compared on the full 64-bit pattern rt_core_dict_float_bits
 * produces rather than by IEEE `==`. Bitwise is what a hash key needs: it is
 * exact (the truncating canon above was not) and it keeps a NaN key findable,
 * which IEEE `==` would not. -0.0/+0.0 stay one key via the fold. */
static int rt_core_dict_key_eq(int64_t a, int64_t b) {
    if (a == b) return 1;
    if (rt_core_is_float(a) || rt_core_is_float(b)) {
        if (!rt_core_is_float(a) || !rt_core_is_float(b)) return 0;
        return rt_core_dict_float_bits(a) == rt_core_dict_float_bits(b);
    }
    return rt_native_eq(a, b) != 0;
}

static void rt_core_dict_resize(RtCoreDict* d, int64_t new_cap) {
    RtCoreDictEntry* old = d->entries;
    int64_t old_cap = d->cap;
    RtCoreDictEntry* fresh = (RtCoreDictEntry*)calloc((size_t)new_cap, sizeof(RtCoreDictEntry));
    if (!fresh) return;
    d->entries = fresh;
    d->cap = new_cap;
    d->len = 0;
    d->tombstones = 0;
    for (int64_t i = 0; i < old_cap; i++) {
        if (old[i].occupied == 1) {
            rt_core_dict_put(d, old[i].key, old[i].value);
        }
    }
    free(old);
}

static int rt_core_dict_put(RtCoreDict* d, int64_t key, int64_t value) {
    if (!d || !d->entries) return 0;
    /* Resize at 70% load (live + tombstones). */
    if ((d->len + d->tombstones + 1) * 10 > d->cap * 7) {
        rt_core_dict_resize(d, d->cap * 2);
    }
    int64_t ck = rt_core_dict_canon_key(key);
    uint64_t h = rt_core_dict_hash(ck);
    int64_t mask = d->cap - 1;
    int64_t idx = (int64_t)(h & (uint64_t)mask);
    int64_t first_tomb = -1;
    for (;;) {
        RtCoreDictEntry* e = &d->entries[idx];
        if (e->occupied == 0) {
            if (first_tomb >= 0) {
                e = &d->entries[first_tomb];
                d->tombstones--;
            }
            e->key = ck;
            e->value = value;
            e->hash = h;
            e->occupied = 1;
            d->len++;
            return 1;
        }
        if (e->occupied == -1) {
            if (first_tomb < 0) first_tomb = idx;
        } else if (e->hash == h && rt_core_dict_key_eq(e->key, ck)) {
            e->value = value;
            return 1;
        }
        idx = (idx + 1) & mask;
    }
}

static int64_t rt_core_dict_lookup(RtCoreDict* d, int64_t key) {
    if (!d || !d->entries || d->len == 0) return rt_core_nil();
    int64_t ck = rt_core_dict_canon_key(key);
    uint64_t h = rt_core_dict_hash(ck);
    int64_t mask = d->cap - 1;
    int64_t idx = (int64_t)(h & (uint64_t)mask);
    for (;;) {
        RtCoreDictEntry* e = &d->entries[idx];
        if (e->occupied == 0) return rt_core_nil();
        if (e->occupied == 1 && e->hash == h && rt_core_dict_key_eq(e->key, ck)) return e->value;
        idx = (idx + 1) & mask;
    }
}

static int rt_core_dict_has(RtCoreDict* d, int64_t key) {
    if (!d || !d->entries || d->len == 0) return 0;
    int64_t ck = rt_core_dict_canon_key(key);
    uint64_t h = rt_core_dict_hash(ck);
    int64_t mask = d->cap - 1;
    int64_t idx = (int64_t)(h & (uint64_t)mask);
    for (;;) {
        RtCoreDictEntry* e = &d->entries[idx];
        if (e->occupied == 0) return 0;
        if (e->occupied == 1 && e->hash == h && rt_core_dict_key_eq(e->key, ck)) return 1;
        idx = (idx + 1) & mask;
    }
}

static int rt_core_dict_del(RtCoreDict* d, int64_t key) {
    if (!d || !d->entries || d->len == 0) return 0;
    int64_t ck = rt_core_dict_canon_key(key);
    uint64_t h = rt_core_dict_hash(ck);
    int64_t mask = d->cap - 1;
    int64_t idx = (int64_t)(h & (uint64_t)mask);
    for (;;) {
        RtCoreDictEntry* e = &d->entries[idx];
        if (e->occupied == 0) return 0;
        if (e->occupied == 1 && e->hash == h && rt_core_dict_key_eq(e->key, ck)) {
            e->occupied = -1;
            d->len--;
            d->tombstones++;
            return 1;
        }
        idx = (idx + 1) & mask;
    }
}

int64_t rt_dict_new(int64_t cap_hint) {
    (void)cap_hint;
    RtCoreDict* d = (RtCoreDict*)calloc(1, sizeof(RtCoreDict));
    if (!d) return rt_core_nil();
    d->kind = RT_VALUE_HEAP_DICT;
    d->cap = RT_CORE_DICT_INIT_CAP;
    d->len = 0;
    d->tombstones = 0;
    d->entries = (RtCoreDictEntry*)calloc((size_t)d->cap, sizeof(RtCoreDictEntry));
    if (!d->entries) {
        free(d);
        return rt_core_nil();
    }
    /* Sole RtCoreDict allocation site -- registering here is what lets
     * rt_core_as_dict test membership before dereferencing ->kind. An
     * unregistered dict would read back as "not a dict", so a failed
     * registration must not produce a live handle. */
    if (!rt_core_register_dict(d)) {
        free(d->entries);
        free(d);
        return rt_core_nil();
    }
    return (int64_t)(((uint64_t)(uintptr_t)d) | RT_VALUE_TAG_HEAP);
}

int64_t rt_dict_get(int64_t dict, int64_t key) {
    return rt_core_dict_lookup(rt_core_as_dict(dict), key);
}

int64_t rt_dict_get_i64_raw(int64_t dict, int64_t key) {
    RtCoreDict* d = rt_core_as_dict(dict);
    int64_t runtime_key = rt_value_int(key);
    if (!rt_core_dict_has(d, runtime_key)) return 0;
    return rt_core_dict_lookup(d, runtime_key);
}

int8_t rt_dict_set(int64_t dict, int64_t key, int64_t value) {
    RtCoreDict* d = rt_core_as_dict(dict);
    if (!d) return 0;
    return (int8_t)rt_core_dict_put(d, key, value);
}

int8_t rt_dict_set_i64_raw(int64_t dict, int64_t key, int64_t value) {
    RtCoreDict* d = rt_core_as_dict(dict);
    if (!d) return 0;
    return (int8_t)rt_core_dict_put(d, rt_value_int(key), value);
}

int8_t rt_dict_insert(int64_t dict, int64_t key, int64_t value) {
    RtCoreDict* d = rt_core_as_dict(dict);
    if (!d) return 0;
    return (int8_t)rt_core_dict_put(d, key, value);
}

int8_t rt_dict_contains(int64_t dict, int64_t key) {
    return (int8_t)rt_core_dict_has(rt_core_as_dict(dict), key);
}

int8_t rt_dict_remove(int64_t dict, int64_t key) {
    return (int8_t)rt_core_dict_del(rt_core_as_dict(dict), key);
}

int8_t rt_dict_clear(int64_t dict) {
    RtCoreDict* d = rt_core_as_dict(dict);
    if (!d || !d->entries) return 0;
    for (int64_t i = 0; i < d->cap; i++) d->entries[i].occupied = 0;
    d->len = 0;
    d->tombstones = 0;
    return 1;
}

int64_t rt_dict_len(int64_t dict) {
    RtCoreDict* d = rt_core_as_dict(dict);
    return d ? d->len : 0;
}

int64_t rt_dict_keys(int64_t dict) {
    RtCoreDict* d = rt_core_as_dict(dict);
    if (!d) return (int64_t)(uintptr_t)rt_array_new(0);
    SplArray* arr = rt_array_new(d->len);
    if (!arr) return rt_core_nil();
    for (int64_t i = 0; i < d->cap; i++) {
        if (d->entries[i].occupied == 1) rt_array_push(arr, d->entries[i].key);
    }
    return (int64_t)(uintptr_t)arr;
}

int64_t rt_dict_values(int64_t dict) {
    RtCoreDict* d = rt_core_as_dict(dict);
    if (!d) return (int64_t)(uintptr_t)rt_array_new(0);
    SplArray* arr = rt_array_new(d->len);
    if (!arr) return rt_core_nil();
    for (int64_t i = 0; i < d->cap; i++) {
        if (d->entries[i].occupied == 1) rt_array_push(arr, d->entries[i].value);
    }
    return (int64_t)(uintptr_t)arr;
}

/* Array of (key, value) 2-tuples — the form `for (k, v) in dict` iterates. */
int64_t rt_dict_entries(int64_t dict) {
    RtCoreDict* d = rt_core_as_dict(dict);
    if (!d) return (int64_t)(uintptr_t)rt_array_new(0);
    SplArray* arr = rt_array_new(d->len);
    if (!arr) return rt_core_nil();
    for (int64_t i = 0; i < d->cap; i++) {
        if (d->entries[i].occupied != 1) continue;
        int64_t pair = rt_tuple_new(2);
        if (pair != rt_core_nil()) {
            rt_tuple_set(pair, 0, d->entries[i].key);
            rt_tuple_set(pair, 1, d->entries[i].value);
        }
        rt_array_push(arr, pair);
    }
    return (int64_t)(uintptr_t)arr;
}

/* Normalize an iterable for index-based for-loops (mirrors the Rust/JIT runtime).
 * Dicts become an array of (key, value) tuples; everything else passes through.
 * Native AOT links the C runtime, which previously lacked this symbol entirely,
 * so `for x in <collection>` called a NULL pointer and SIGSEGV'd. */
int64_t rt_for_iterable(int64_t collection) {
    if (rt_core_as_dict(collection)) return rt_dict_entries(collection);
    /* Text becomes its UTF-8 codepoint array, so `for ch in <text>` binds one
     * 1-char text per codepoint. Without this, a string fell through to the
     * generic rt_array_len / IndexGet path, which read the BYTE length and
     * indexed raw bytes: "café,"-style input ran 6 times instead of 5 and
     * bound garbage that concatenated to nothing. Keep in sync with
     * rt_for_iterable in src/runtime/simple_core/core_array.spl. */
    if (rt_core_as_string(collection)) return rt_string_chars(collection);
    return collection;
}

/* ================================================================
 * File I/O (wrappers around existing rt_/spl_ functions)
 * ================================================================ */

/* rt_file_read_text, rt_file_exists, rt_file_delete, rt_env_get are
 * defined in runtime.c when the full runtime is linked, but the
 * core-c-bootstrap build only includes runtime_legacy_core.c
 * (not runtime.c).  Provide them here so that
 * native CLI binaries built against the core-c runtime can read files
 * and query the environment without segfaulting on nil stubs. */

static char* rt_core_string_to_cpath(int64_t value);

/* ---------------------------------------------------------------------------
 * `text` extern ABI helper -- mirrors rt_text_arg_to_path in runtime.c.
 *
 * The compiler emits TWO machine words for every `text` extern argument,
 * (ptr, len): see RuntimeFuncSpec in
 * src/compiler_rust/compiler/src/codegen/runtime_sffi.rs and the decomposition
 * in src/compiler/50.mir/text_extern_abi.spl. A Simple `text` is NOT
 * NUL-terminated, so a `const char*` parameter reads past the end of the value.
 * That is the rt_file_is_char_device defect (fixed 81fca37cdd4); every rt_*
 * path entry point must copy through this helper before calling libc.
 * ------------------------------------------------------------------------- */
#define RT_TEXT_PATH_MAX 4096
static int rt_text_arg_to_path(const uint8_t* ptr, uint64_t len, char* buf, size_t buf_size) {
    if (!ptr && len != 0) return 0;
    if (len >= (uint64_t)buf_size) return 0;
    if (len != 0) memcpy(buf, ptr, (size_t)len);
    buf[(size_t)len] = '\0';
    return 1;
}

/* (ptr, len) -> RuntimeValue: see rt_text_arg_to_path above.
 *
 * runtime_sffi.rs:1852 declares `&[I64, I64] -> &[I64]`; the result is a
 * RuntimeValue, not a raw C string. This copy used to return the malloc'd
 * `char*` straight out of spl_file_read, which the caller then decoded as a
 * tagged value -- see the sibling comment in runtime.c. */
int64_t rt_file_read_text(const uint8_t* path_ptr, uint64_t path_len) {
    char path[RT_TEXT_PATH_MAX];
    /* RT_NIL == 3 (TAG_SPECIAL, payload 0); == RuntimeValue::NIL. */
    const int64_t rt_nil = 3;
    if (!rt_text_arg_to_path(path_ptr, path_len, path, sizeof(path))) return rt_nil;
    /* spl_file_read returns "" (not NULL) on open failure; the Rust definition
     * returns NIL, and Simple's `?? ""` only fires on nil. Probe openability. */
    { FILE* probe = fopen(path, "rb"); if (!probe) return rt_nil; fclose(probe); }
    char* content = spl_file_read(path);
    if (!content) return rt_nil;
    int64_t result = rt_string_new((const uint8_t*)content, (uint64_t)strlen(content));
    free(content);
    return result;
}

int64_t rt_file_read_text_rv(int64_t path_value) {
    char* path = rt_core_string_to_cpath(path_value);
    if (!path) return rt_string_new(NULL, 0);
    char* content = spl_file_read(path);
    free(path);
    if (!content) return rt_string_new(NULL, 0);
    size_t len = strlen(content);
    int64_t result = rt_string_new((const uint8_t*)content, (uint64_t)len);
    free(content);
    return result;
}

/*
 * Native Simple-core compatibility is intentionally a facade-only counter:
 * no libc/syscall worker is instrumented.  Its C implementation follows the
 * same accepting/lease/generation protocol as runtime.c.  The pure-Simple
 * interpreter provider documents single-thread, fail-closed parity instead
 * of claiming this native atomic drain contract.
 */
#define RT_FILE_EXISTS_PROBE_ACCEPTING    (UINT64_C(1) << 63)
#define RT_FILE_EXISTS_PROBE_TRANSITION   (UINT64_C(1) << 62)
#define RT_FILE_EXISTS_PROBE_LEASE_MASK   (RT_FILE_EXISTS_PROBE_TRANSITION - 1)
#define RT_FILE_EXISTS_PROBE_GENERATION_MAX UINT64_C(0x7fffffffffffffff)
#define RT_FILE_EXISTS_PROBE_TOTAL_MAX    UINT64_C(0x7fffffff)

static atomic_uint_fast64_t rt_file_exists_probe_state = ATOMIC_VAR_INIT(0);
static atomic_uint_fast64_t rt_file_exists_probe_generation = ATOMIC_VAR_INIT(0);
static atomic_uint_fast64_t rt_file_exists_probe_total = ATOMIC_VAR_INIT(0);
static atomic_uint_fast64_t rt_file_exists_probe_failed = ATOMIC_VAR_INIT(0);

/* Reserve one total slot. A failed slot is incremented only after this succeeds,
 * so concurrent records preserve failed <= total <= TOTAL_MAX. */
static int rt_file_exists_probe_try_add_total(void) {
    uint_fast64_t current = atomic_load_explicit(
        &rt_file_exists_probe_total, memory_order_relaxed);
    while (current < RT_FILE_EXISTS_PROBE_TOTAL_MAX) {
        if (atomic_compare_exchange_weak_explicit(
                &rt_file_exists_probe_total, &current, current + 1,
                memory_order_relaxed, memory_order_relaxed)) {
            return 1;
        }
    }
    return 0;
}

static uint_fast64_t rt_file_exists_probe_lease_admit(void) {
    /* Disabled source path: one relaxed gate load, without assembly claims. */
    uint_fast64_t state = atomic_load_explicit(
        &rt_file_exists_probe_state, memory_order_relaxed);
    if ((state & RT_FILE_EXISTS_PROBE_ACCEPTING) == 0) return 0;

    for (;;) {
        if ((state & RT_FILE_EXISTS_PROBE_ACCEPTING) == 0) return 0;
        if ((state & RT_FILE_EXISTS_PROBE_LEASE_MASK) ==
            RT_FILE_EXISTS_PROBE_LEASE_MASK) return 0;
        if (atomic_compare_exchange_weak_explicit(
                &rt_file_exists_probe_state, &state, state + UINT64_C(1),
                memory_order_acquire, memory_order_relaxed)) {
            uint_fast64_t generation = atomic_load_explicit(
                &rt_file_exists_probe_generation, memory_order_acquire);
            if (generation != 0) return generation;
            atomic_fetch_sub_explicit(
                &rt_file_exists_probe_state, UINT64_C(1), memory_order_release);
            return 0;
        }
    }
}

static void rt_file_exists_probe_record(uint_fast64_t lease, int exists) {
    if (lease != 0 && atomic_load_explicit(
            &rt_file_exists_probe_generation, memory_order_acquire) == lease) {
        if (rt_file_exists_probe_try_add_total() && !exists) {
            uint_fast64_t failed = atomic_load_explicit(
                &rt_file_exists_probe_failed, memory_order_relaxed);
            while (failed < RT_FILE_EXISTS_PROBE_TOTAL_MAX) {
                if (atomic_compare_exchange_weak_explicit(
                        &rt_file_exists_probe_failed, &failed, failed + 1,
                        memory_order_relaxed, memory_order_relaxed)) {
                    break;
                }
            }
        }
    }
    if (lease != 0) {
        atomic_fetch_sub_explicit(
            &rt_file_exists_probe_state, UINT64_C(1), memory_order_release);
    }
}

int64_t rt_file_exists_probe_begin(void) {
    uint_fast64_t idle = 0;
    if (!atomic_compare_exchange_strong_explicit(
            &rt_file_exists_probe_state, &idle, RT_FILE_EXISTS_PROBE_TRANSITION,
            memory_order_acq_rel, memory_order_acquire)) {
        return -1;
    }
    uint_fast64_t generation = atomic_load_explicit(
        &rt_file_exists_probe_generation, memory_order_acquire);
    if (generation >= RT_FILE_EXISTS_PROBE_GENERATION_MAX) {
        atomic_store_explicit(&rt_file_exists_probe_state, 0, memory_order_release);
        return -3;
    }
    generation += 1;
    atomic_store_explicit(
        &rt_file_exists_probe_generation, generation, memory_order_release);
    atomic_store_explicit(&rt_file_exists_probe_total, 0, memory_order_relaxed);
    atomic_store_explicit(&rt_file_exists_probe_failed, 0, memory_order_relaxed);
    atomic_store_explicit(
        &rt_file_exists_probe_state, RT_FILE_EXISTS_PROBE_ACCEPTING,
        memory_order_release);
    return (int64_t)generation;
}

int64_t rt_file_exists_probe_end(int64_t token) {
    if (token <= 0 || (uint_fast64_t)token > RT_FILE_EXISTS_PROBE_GENERATION_MAX ||
        atomic_load_explicit(&rt_file_exists_probe_generation, memory_order_acquire) !=
            (uint_fast64_t)token) return -2;

    uint_fast64_t state = atomic_load_explicit(
        &rt_file_exists_probe_state, memory_order_acquire);
    for (;;) {
        if ((state & RT_FILE_EXISTS_PROBE_ACCEPTING) == 0 ||
            atomic_load_explicit(&rt_file_exists_probe_generation, memory_order_acquire) !=
                (uint_fast64_t)token) {
            return -2;
        }
        uint_fast64_t closing =
            (state & RT_FILE_EXISTS_PROBE_LEASE_MASK) |
            RT_FILE_EXISTS_PROBE_TRANSITION;
        if (atomic_compare_exchange_weak_explicit(
                &rt_file_exists_probe_state, &state, closing,
                memory_order_acq_rel, memory_order_acquire)) {
            break;
        }
    }

    do {
        state = atomic_load_explicit(
            &rt_file_exists_probe_state, memory_order_acquire);
    } while ((state & RT_FILE_EXISTS_PROBE_LEASE_MASK) != 0);

    uint_fast64_t total = atomic_load_explicit(
        &rt_file_exists_probe_total, memory_order_acquire);
    uint_fast64_t failed = atomic_load_explicit(
        &rt_file_exists_probe_failed, memory_order_acquire);
    if (total > RT_FILE_EXISTS_PROBE_TOTAL_MAX) total = RT_FILE_EXISTS_PROBE_TOTAL_MAX;
    if (failed > RT_FILE_EXISTS_PROBE_TOTAL_MAX) {
        failed = RT_FILE_EXISTS_PROBE_TOTAL_MAX;
    }
    atomic_store_explicit(
        &rt_file_exists_probe_state,
        0,
        memory_order_release);
    return (int64_t)((total << 32) | failed);
}

#if defined(SIMPLE_RUNTIME_TESTING)
int64_t rt_file_exists_probe_test_seed_generation(int64_t generation) {
    if (generation < 0 || (uint_fast64_t)generation >
            RT_FILE_EXISTS_PROBE_GENERATION_MAX) return -3;
    uint_fast64_t idle = 0;
    if (!atomic_compare_exchange_strong_explicit(
            &rt_file_exists_probe_state, &idle, RT_FILE_EXISTS_PROBE_TRANSITION,
            memory_order_acq_rel, memory_order_acquire)) return -1;
    atomic_store_explicit(
        &rt_file_exists_probe_generation, (uint_fast64_t)generation,
        memory_order_release);
    atomic_store_explicit(&rt_file_exists_probe_total, 0, memory_order_relaxed);
    atomic_store_explicit(&rt_file_exists_probe_failed, 0, memory_order_relaxed);
    atomic_store_explicit(&rt_file_exists_probe_state, 0, memory_order_release);
    return 0;
}

int64_t rt_file_exists_probe_test_seed_counters(int64_t total, int64_t failed) {
    if (total < 0 || failed < 0 || (uint_fast64_t)total >
            RT_FILE_EXISTS_PROBE_TOTAL_MAX || (uint_fast64_t)failed >
            (uint_fast64_t)total) return -3;
    uint_fast64_t state = atomic_load_explicit(
        &rt_file_exists_probe_state, memory_order_acquire);
    if ((state & RT_FILE_EXISTS_PROBE_ACCEPTING) == 0 ||
        (state & RT_FILE_EXISTS_PROBE_LEASE_MASK) != 0) return -1;
    atomic_store_explicit(
        &rt_file_exists_probe_total, (uint_fast64_t)total, memory_order_relaxed);
    atomic_store_explicit(
        &rt_file_exists_probe_failed, (uint_fast64_t)failed, memory_order_relaxed);
    return 0;
}
#endif

int rt_file_exists(const uint8_t* path_ptr, uint64_t path_len) {
    uint_fast64_t lease = rt_file_exists_probe_lease_admit();
    char path[RT_TEXT_PATH_MAX];
    int exists = 0;
    if (rt_text_arg_to_path(path_ptr, path_len, path, sizeof(path))) {
        FILE* f = fopen(path, "r");
        if (f) { fclose(f); exists = 1; }
    }
    rt_file_exists_probe_record(lease, exists);
    return exists;
}

int rt_file_is_regular_no_follow(const uint8_t* path_ptr, uint64_t path_len) {
    char path_buf[RT_TEXT_PATH_MAX];
    if (!rt_text_arg_to_path(path_ptr, path_len, path_buf, sizeof(path_buf))) return 0;
    const char* path = path_buf;
#if defined(_WIN32)
    if (!path) return 0;
    int wide_len = MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, path, -1, NULL, 0);
    if (wide_len <= 0) return 0;
    wchar_t* wide_path = (wchar_t*)malloc((size_t)wide_len * sizeof(wchar_t));
    if (!wide_path) return 0;
    if (!MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, path, -1, wide_path, wide_len)) {
        free(wide_path);
        return 0;
    }
    DWORD attributes = GetFileAttributesW(wide_path);
    free(wide_path);
    return attributes != INVALID_FILE_ATTRIBUTES &&
           (attributes & (FILE_ATTRIBUTE_DIRECTORY | FILE_ATTRIBUTE_REPARSE_POINT)) == 0;
#else
    struct stat st;
    return path && lstat(path, &st) == 0 && S_ISREG(st.st_mode);
#endif
}

/* rt_file_is_char_device: mirrors runtime.c's rt_file_is_char_device for the
 * core-c-bootstrap build (native binaries linked without runtime.c). See
 * that definition for rationale (no-shell char-device probe, symlinks
 * followed). */
int rt_file_is_char_device(const uint8_t* path_ptr, uint64_t path_len) {
#if defined(_WIN32)
    (void)path_ptr; (void)path_len;
    return 0;
#else
    /* The compiler emits the two-argument (ptr, len) form for `text` externs
     * (runtime_sffi.rs / src/compiler/50.mir/text_extern_abi.spl); a Simple
     * `text` is NOT NUL-terminated, so the buffer must be copied. */
    char buf[4096];
    if (!path_ptr || path_len >= sizeof(buf)) return 0;
    memcpy(buf, path_ptr, (size_t)path_len);
    buf[(size_t)path_len] = '\0';
    struct stat st;
    return stat(buf, &st) == 0 && S_ISCHR(st.st_mode);
#endif
}

int rt_file_delete(const char* path) {
    if (!path) return 0;
    return remove(path) == 0 ? 1 : 0;
}

int rt_file_remove(const uint8_t* path_ptr, uint64_t path_len) {
    if (!path_ptr || path_len > SIZE_MAX - 1) return 0;
    char* path = (char*)malloc((size_t)path_len + 1);
    if (!path) return 0;
    memcpy(path, path_ptr, (size_t)path_len);
    path[(size_t)path_len] = '\0';
    int ok = remove(path) == 0 ? 1 : 0;
    free(path);
    return ok;
}

/* Non-accelerator native bridges. Text parameters use the ABI selected by
 * the caller: path_parent is (ptr, len); the legacy filename/extension
 * aliases receive a tagged RuntimeValue. */
int64_t rt_path_parent(const uint8_t* path_ptr, int64_t path_len) {
    if (!path_ptr || path_len <= 0) return rt_string_new(NULL, 0);
    int64_t end = path_len;
    while (end > 1 && path_ptr[end - 1] == '/') end--;
    int64_t slash = end - 1;
    while (slash >= 0 && path_ptr[slash] != '/') slash--;
    if (slash < 0) return rt_string_new((const uint8_t*)".", 1);
    if (slash == 0) return rt_string_new(path_ptr, 1);
    return rt_string_new(path_ptr, (uint64_t)slash);
}

int64_t rt_path_absolute(const uint8_t* path_ptr, uint64_t path_len) {
    if (!path_ptr || path_len > (uint64_t)SIZE_MAX - 1) {
        return rt_string_new(NULL, 0);
    }
    char* path = (char*)malloc((size_t)path_len + 1);
    if (!path) return rt_string_new(NULL, 0);
    memcpy(path, path_ptr, (size_t)path_len);
    path[(size_t)path_len] = '\0';

#if defined(_WIN32)
    char* absolute = _fullpath(NULL, path, 0);
#else
    char* absolute = realpath(path, NULL);
#endif
    if (!absolute) {
        bool already_absolute = path[0] == '/';
#if defined(_WIN32)
        already_absolute = already_absolute ||
            (path_len >= 3 && path[1] == ':' &&
             (path[2] == '/' || path[2] == '\\'));
#endif
        if (already_absolute) {
            absolute = spl_strdup(path);
        } else {
            char* cwd = rt_getcwd();
            if (cwd) {
                size_t cwd_len = strlen(cwd);
                if (cwd_len <= SIZE_MAX - 2 &&
                        (size_t)path_len <= SIZE_MAX - cwd_len - 2) {
                    absolute = (char*)malloc(cwd_len + (size_t)path_len + 2);
                }
                if (absolute) {
                    memcpy(absolute, cwd, cwd_len);
#if defined(_WIN32)
                    absolute[cwd_len] = '\\';
#else
                    absolute[cwd_len] = '/';
#endif
                    memcpy(absolute + cwd_len + 1, path, (size_t)path_len + 1);
                }
                free(cwd);
            }
        }
    }
    free(path);
    if (!absolute) return rt_string_new(path_ptr, path_len);
    int64_t result = rt_string_new((const uint8_t*)absolute, strlen(absolute));
    free(absolute);
    return result;
}

int64_t rt_path_filename(int64_t path_value) {
    RtCoreString* path = rt_core_as_string(path_value);
    if (!path || path->len == 0) return rt_string_new(NULL, 0);
    uint64_t end = path->len;
    while (end > 0 && path->data[end - 1] == '/') end--;
    if (end == 0) return rt_string_new(NULL, 0);
    uint64_t start = end;
    while (start > 0 && path->data[start - 1] != '/') start--;
    return rt_string_new((const uint8_t*)path->data + start, end - start);
}

int64_t rt_path_extension(int64_t path_value) {
    RtCoreString* path = rt_core_as_string(path_value);
    if (!path || path->len == 0) return rt_string_new(NULL, 0);
    uint64_t end = path->len;
    while (end > 0 && path->data[end - 1] == '/') end--;
    uint64_t start = end;
    while (start > 0 && path->data[start - 1] != '/') start--;
    uint64_t dot = end;
    while (dot > start && path->data[dot - 1] != '.') dot--;
    if (dot == start || (dot == start + 1 && path->data[start] == '.')) {
        return rt_string_new(NULL, 0);
    }
    return rt_string_new((const uint8_t*)path->data + dot, end - dot);
}

void rt_sleep_secs(int64_t seconds) {
    if (seconds <= 0) return;
    rt_sleep_ms_native(seconds > INT64_MAX / 1000 ? INT64_MAX : seconds * 1000);
}

static int64_t rt_http_tuple(int64_t status, const uint8_t* body, uint64_t body_len,
                             const char* error) {
    int64_t tuple = rt_tuple_new(3);
    if (tuple == rt_core_nil()) return rt_core_nil();
    rt_tuple_set(tuple, 0, rt_value_int(status));
    rt_tuple_set(tuple, 1, rt_string_new(body, body_len));
    rt_tuple_set(tuple, 2, rt_string_new((const uint8_t*)(error ? error : ""),
                                         error ? (uint64_t)strlen(error) : 0));
    return tuple;
}

static int64_t rt_http_download_tuple(int64_t status, uint64_t bytes, const char* error) {
    int64_t tuple = rt_tuple_new(3);
    if (tuple == rt_core_nil()) return rt_core_nil();
    rt_tuple_set(tuple, 0, rt_value_int(status));
    rt_tuple_set(tuple, 1, rt_value_int((int64_t)bytes));
    rt_tuple_set(tuple, 2, rt_string_new((const uint8_t*)(error ? error : ""),
                                         error ? (uint64_t)strlen(error) : 0));
    return tuple;
}

#define RT_HTTP_CLIENT_CAPACITY 64
#define RT_HTTP_CLIENT_SLOT_BITS 8

typedef struct {
    uint64_t generation;
    int64_t timeout_ms;
    int in_use;
} RtHttpClientSlot;

static RtHttpClientSlot rt_http_clients[RT_HTTP_CLIENT_CAPACITY];
static atomic_flag rt_http_clients_lock = ATOMIC_FLAG_INIT;
static uint64_t rt_http_client_next_generation = 1;

static void rt_http_clients_acquire(void) {
    while (atomic_flag_test_and_set_explicit(&rt_http_clients_lock, memory_order_acquire)) {}
}

static void rt_http_clients_release(void) {
    atomic_flag_clear_explicit(&rt_http_clients_lock, memory_order_release);
}

static int rt_http_client_slot(int64_t handle, uint64_t* generation) {
    uint64_t raw = (uint64_t)handle;
    uint64_t encoded_slot = raw & ((1u << RT_HTTP_CLIENT_SLOT_BITS) - 1u);
    if (handle <= 0 || encoded_slot == 0 || encoded_slot > RT_HTTP_CLIENT_CAPACITY) return -1;
    *generation = raw >> RT_HTTP_CLIENT_SLOT_BITS;
    return (int)encoded_slot - 1;
}

static int rt_http_client_timeout(int64_t handle, int64_t* timeout_ms) {
    uint64_t generation = 0;
    int slot = rt_http_client_slot(handle, &generation);
    if (slot < 0) return 0;
    rt_http_clients_acquire();
    RtHttpClientSlot* client = &rt_http_clients[slot];
    int valid = client->in_use && client->generation == generation;
    if (valid) *timeout_ms = client->timeout_ms;
    rt_http_clients_release();
    return valid;
}

int64_t rt_http_client_create(void) {
    rt_http_clients_acquire();
    for (int slot = 0; slot < RT_HTTP_CLIENT_CAPACITY; slot++) {
        if (rt_http_clients[slot].in_use) continue;
        uint64_t generation = rt_http_client_next_generation++;
        if (generation == 0 || generation > ((uint64_t)INT64_MAX >> RT_HTTP_CLIENT_SLOT_BITS)) {
            generation = 1;
            rt_http_client_next_generation = 2;
        }
        rt_http_clients[slot].generation = generation;
        rt_http_clients[slot].timeout_ms = 0;
        rt_http_clients[slot].in_use = 1;
        int64_t handle = (int64_t)((generation << RT_HTTP_CLIENT_SLOT_BITS) | (uint64_t)(slot + 1));
        rt_http_clients_release();
        return handle;
    }
    rt_http_clients_release();
    return 0;
}

bool rt_http_client_set_timeout(int64_t handle, int64_t timeout_ms) {
    if (timeout_ms < 0) return false;
    uint64_t generation = 0;
    int slot = rt_http_client_slot(handle, &generation);
    if (slot < 0) return false;
    rt_http_clients_acquire();
    RtHttpClientSlot* client = &rt_http_clients[slot];
    bool valid = client->in_use && client->generation == generation;
    if (valid) client->timeout_ms = timeout_ms;
    rt_http_clients_release();
    return valid;
}

void rt_http_client_destroy(int64_t handle) {
    uint64_t generation = 0;
    int slot = rt_http_client_slot(handle, &generation);
    if (slot < 0) return;
    rt_http_clients_acquire();
    RtHttpClientSlot* client = &rt_http_clients[slot];
    if (client->in_use && client->generation == generation) {
        client->in_use = 0;
        client->timeout_ms = 0;
    }
    rt_http_clients_release();
}

#if !defined(_WIN32)
static int rt_http_remaining_ms(int64_t deadline_ms) {
    if (deadline_ms == 0) return -1;
    int64_t remaining = deadline_ms - rt_time_now_monotonic_ms();
    if (remaining <= 0) {
        errno = ETIMEDOUT;
        return 0;
    }
    return remaining > INT32_MAX ? INT32_MAX : (int)remaining;
}

static int rt_http_wait_fd(int fd, short events, int64_t deadline_ms) {
    if (deadline_ms == 0) return 1;
    for (;;) {
        int timeout_ms = rt_http_remaining_ms(deadline_ms);
        if (timeout_ms == 0) return 0;
        struct pollfd poll_fd = {.fd = fd, .events = events};
        int result = poll(&poll_fd, 1, timeout_ms);
        if (result > 0) return (poll_fd.revents & (events | POLLERR | POLLHUP)) != 0;
        if (result == 0) errno = ETIMEDOUT;
        if (result >= 0 || errno != EINTR) return 0;
    }
}

typedef struct {
    atomic_int refs;
    atomic_int done;
    char* host;
    char* port;
    struct addrinfo hints;
    struct addrinfo* results;
    int result_code;
    int result_errno;
    int notify_read_fd;
    int notify_write_fd;
} RtHttpResolveJob;

static void rt_http_resolve_job_release(RtHttpResolveJob* job) {
    if (atomic_fetch_sub_explicit(&job->refs, 1, memory_order_acq_rel) != 1) return;
    if (job->results) freeaddrinfo(job->results);
    close(job->notify_read_fd);
    free(job->host); free(job->port); free(job);
}

static void* rt_http_resolve_worker(void* context) {
    RtHttpResolveJob* job = (RtHttpResolveJob*)context;
    errno = 0;
    job->result_code = getaddrinfo(job->host, job->port, &job->hints, &job->results);
    job->result_errno = errno;
    atomic_store_explicit(&job->done, 1, memory_order_release);
    char completed = 1;
    while (write(job->notify_write_fd, &completed, 1) < 0 && errno == EINTR) {}
    close(job->notify_write_fd);
    rt_http_resolve_job_release(job);
    return NULL;
}

static int rt_http_resolve(const char* host, const char* port, const struct addrinfo* hints,
                           int64_t deadline_ms, struct addrinfo** results_out) {
    if (deadline_ms == 0) return getaddrinfo(host, port, hints, results_out);
    if (rt_http_remaining_ms(deadline_ms) == 0) return EAI_SYSTEM;

    RtHttpResolveJob* job = (RtHttpResolveJob*)calloc(1, sizeof(*job));
    if (!job) return EAI_MEMORY;
    job->host = strdup(host);
    job->port = strdup(port);
    int notify[2] = {-1, -1};
    if (!job->host || !job->port || pipe(notify) != 0) {
        free(job->host); free(job->port); free(job); return EAI_SYSTEM;
    }
    job->notify_read_fd = notify[0];
    job->notify_write_fd = notify[1];
    job->hints = *hints;
    atomic_init(&job->refs, 2);
    atomic_init(&job->done, 0);

    pthread_attr_t thread_attr;
    if (pthread_attr_init(&thread_attr) != 0) {
        close(notify[0]); close(notify[1]); free(job->host); free(job->port); free(job);
        return EAI_SYSTEM;
    }
    if (pthread_attr_setdetachstate(&thread_attr, PTHREAD_CREATE_DETACHED) != 0) {
        pthread_attr_destroy(&thread_attr);
        close(notify[0]); close(notify[1]); free(job->host); free(job->port); free(job);
        return EAI_SYSTEM;
    }
    pthread_t thread;
    int create_result = pthread_create(&thread, &thread_attr, rt_http_resolve_worker, job);
    pthread_attr_destroy(&thread_attr);
    if (create_result != 0) {
        close(notify[0]); close(notify[1]); free(job->host); free(job->port); free(job);
        errno = create_result;
        return EAI_SYSTEM;
    }

    struct pollfd completion = {.fd = job->notify_read_fd, .events = POLLIN};
    for (;;) {
        int remaining_ms = rt_http_remaining_ms(deadline_ms);
        if (remaining_ms == 0) break;
        int wait_result = poll(&completion, 1, remaining_ms);
        if (wait_result > 0 && atomic_load_explicit(&job->done, memory_order_acquire)) break;
        if (wait_result < 0 && errno == EINTR) continue;
        if (wait_result == 0) errno = ETIMEDOUT;
        break;
    }
    if (!atomic_load_explicit(&job->done, memory_order_acquire) ||
        rt_http_remaining_ms(deadline_ms) == 0) {
        errno = ETIMEDOUT;
        rt_http_resolve_job_release(job);
        return EAI_SYSTEM;
    }
    int result_code = job->result_code;
    errno = job->result_errno;
    if (result_code == 0) { *results_out = job->results; job->results = NULL; }
    rt_http_resolve_job_release(job);
    return result_code;
}

static void rt_http_set_socket_timeout(int fd, int64_t deadline_ms) {
    int remaining = rt_http_remaining_ms(deadline_ms);
    if (remaining <= 0) return;
    struct timeval timeout = {.tv_sec = remaining / 1000, .tv_usec = (remaining % 1000) * 1000};
    (void)setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &timeout, sizeof(timeout));
    (void)setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &timeout, sizeof(timeout));
}

static int rt_http_send_all(int fd, const void* data, size_t len, int64_t deadline_ms) {
    const uint8_t* ptr = (const uint8_t*)data;
    while (len > 0) {
        if (!rt_http_wait_fd(fd, POLLOUT, deadline_ms)) return 0;
        ssize_t sent = send(fd, ptr, len, 0);
        if (sent < 0 && errno == EINTR) continue;
        if (sent < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) continue;
        if (sent <= 0) return 0;
        ptr += (size_t)sent;
        len -= (size_t)sent;
    }
    return 1;
}

static int rt_http_append(char** dst, size_t* len, size_t* cap,
                          const char* text, size_t text_len) {
    if (*len > SIZE_MAX - text_len - 1) return 0;
    size_t need = *len + text_len + 1;
    if (need > *cap) {
        size_t next = *cap ? *cap : 1024;
        while (next < need) {
            if (next > SIZE_MAX / 2) return 0;
            next *= 2;
        }
        char* grown = (char*)realloc(*dst, next);
        if (!grown) return 0;
        *dst = grown;
        *cap = next;
    }
    memcpy(*dst + *len, text, text_len);
    *len += text_len;
    (*dst)[*len] = '\0';
    return 1;
}

static const char* rt_http_header_end(const uint8_t* data, size_t len) {
    if (!data || len < 4) return NULL;
    for (size_t i = 0; i + 4 <= len; i++) {
        if (memcmp(data + i, "\r\n\r\n", 4) == 0) return (const char*)data + i;
    }
    return NULL;
}

static int rt_http_has_header(const char* headers, size_t len, const char* name) {
    size_t name_len = strlen(name);
    const char* line = headers;
    const char* end = headers + len;
    while (line < end) {
        const char* next = strstr(line, "\r\n");
        if (!next || next > end) next = end;
        if ((size_t)(next - line) > name_len &&
            strncasecmp(line, name, name_len) == 0 && line[name_len] == ':') return 1;
        line = next < end ? next + 2 : end;
    }
    return 0;
}

static int64_t rt_http_content_length(const char* headers, size_t len) {
    const char* line = headers;
    const char* end = headers + len;
    while (line < end) {
        const char* next = strstr(line, "\r\n");
        if (!next || next > end) next = end;
        if ((size_t)(next - line) >= 15 && strncasecmp(line, "Content-Length:", 15) == 0) {
            const char* value = line + 15;
            while (value < next && (*value == ' ' || *value == '\t')) value++;
            char* parse_end = NULL;
            unsigned long long parsed = strtoull(value, &parse_end, 10);
            if (parse_end == value || parsed > (unsigned long long)INT64_MAX) return -1;
            return (int64_t)parsed;
        }
        line = next < end ? next + 2 : end;
    }
    return -1;
}

static int rt_http_decode_chunked(const uint8_t* src, size_t src_len,
                                  uint8_t** out, size_t* out_len) {
    size_t pos = 0, used = 0, cap = src_len;
    uint8_t* result = cap ? (uint8_t*)malloc(cap) : NULL;
    if (cap && !result) return 0;
    while (pos < src_len) {
        size_t line_start = pos;
        while (pos + 1 < src_len && !(src[pos] == '\r' && src[pos + 1] == '\n')) pos++;
        if (pos + 1 >= src_len) { free(result); return 0; }
        size_t size_len = pos - line_start;
        const uint8_t* semi = memchr(src + line_start, ';', size_len);
        if (semi) size_len = (size_t)(semi - (src + line_start));
        char size_text[32];
        if (size_len == 0 || size_len >= sizeof(size_text)) { free(result); return 0; }
        memcpy(size_text, src + line_start, size_len); size_text[size_len] = '\0';
        char* parse_end = NULL;
        unsigned long long chunk = strtoull(size_text, &parse_end, 16);
        if (parse_end == size_text || chunk > SIZE_MAX) { free(result); return 0; }
        pos += 2;
        if (chunk == 0) break;
        if ((size_t)chunk > src_len - pos || used > SIZE_MAX - (size_t)chunk) {
            free(result); return 0;
        }
        if (used + (size_t)chunk > cap) {
            uint8_t* grown = (uint8_t*)realloc(result, used + (size_t)chunk);
            if (!grown) { free(result); return 0; }
            result = grown; cap = used + (size_t)chunk;
        }
        memcpy(result + used, src + pos, (size_t)chunk); used += (size_t)chunk; pos += (size_t)chunk;
        if (pos + 1 >= src_len || src[pos] != '\r' || src[pos + 1] != '\n') {
            free(result); return 0;
        }
        pos += 2;
    }
    *out = result; *out_len = used; return 1;
}

static int rt_http_method_is_token(const char* method) {
    if (!method || !*method) return 0;
    for (const unsigned char* p = (const unsigned char*)method; *p; p++) {
        if (!(('0' <= *p && *p <= '9') || ('A' <= *p && *p <= 'Z') ||
              ('a' <= *p && *p <= 'z') || strchr("!#$%&'*+-.^_`|~", *p))) return 0;
    }
    return 1;
}

static int rt_http_perform(const char* method, const char* url, RtCoreArray* headers,
                           const uint8_t* body, size_t body_len, int64_t timeout_ms,
                           int64_t* status_out,
                           uint8_t** body_out, size_t* body_len_out, char* error, size_t error_cap) {
    *status_out = -1; *body_out = NULL; *body_len_out = 0;
    int64_t deadline_ms = 0;
    if (timeout_ms > 0) {
        int64_t now = rt_time_now_monotonic_ms();
        deadline_ms = timeout_ms > INT64_MAX - now ? INT64_MAX : now + timeout_ms;
    }
    if (!rt_http_method_is_token(method) || !url) {
        snprintf(error, error_cap, "invalid HTTP method or URL"); return 0;
    }
    for (const unsigned char* p = (const unsigned char*)url; *p; p++) {
        if (*p <= 0x20 || *p == 0x7f) {
            snprintf(error, error_cap, "invalid HTTP URL"); return 0;
        }
    }
    if (strncmp(url, "http://", 7) != 0) {
        snprintf(error, error_cap, "native HTTP supports http:// only; HTTPS requires the TLS runtime"); return 0;
    }
    const char* authority = url + 7;
    const char* target = strpbrk(authority, "/?#");
    const char* authority_end = target ? target : authority + strlen(authority);
    if (authority_end == authority) { snprintf(error, error_cap, "HTTP URL has no host"); return 0; }
    size_t authority_len = (size_t)(authority_end - authority);
    char* host_port = (char*)malloc(authority_len + 1);
    if (!host_port) { snprintf(error, error_cap, "out of memory"); return 0; }
    memcpy(host_port, authority, authority_len); host_port[authority_len] = '\0';
    int port = 80;
    char* colon = strrchr(host_port, ':');
    if (colon && colon[1] != '\0') {
        char* parse_end = NULL; long parsed = strtol(colon + 1, &parse_end, 10);
        if (*parse_end != '\0' || parsed < 1 || parsed > 65535) {
            free(host_port); snprintf(error, error_cap, "invalid HTTP port"); return 0;
        }
        *colon = '\0'; port = (int)parsed;
    }
    if (!host_port[0]) { free(host_port); snprintf(error, error_cap, "HTTP URL has no host"); return 0; }
    char port_text[8]; snprintf(port_text, sizeof(port_text), "%d", port);
    struct addrinfo hints, *results = NULL;
    memset(&hints, 0, sizeof(hints)); hints.ai_socktype = SOCK_STREAM;
    errno = 0;
    if (rt_http_resolve(host_port, port_text, &hints, deadline_ms, &results) != 0) {
        free(host_port);
        snprintf(error, error_cap, errno == ETIMEDOUT ? "HTTP request timed out" : "HTTP host lookup failed");
        return 0;
    }
    int fd = -1;
    for (struct addrinfo* item = results; item; item = item->ai_next) {
        if (deadline_ms != 0 && rt_http_remaining_ms(deadline_ms) == 0) break;
        fd = socket(item->ai_family, item->ai_socktype, item->ai_protocol);
        if (fd < 0) continue;
        if (deadline_ms != 0) {
            int flags = fcntl(fd, F_GETFL, 0);
            if (flags < 0 || fcntl(fd, F_SETFL, flags | O_NONBLOCK) != 0) {
                close(fd); fd = -1; continue;
            }
        }
        int connected = connect(fd, item->ai_addr, item->ai_addrlen) == 0;
        if (!connected && deadline_ms != 0 && errno == EINPROGRESS &&
            rt_http_wait_fd(fd, POLLOUT, deadline_ms)) {
            int socket_error = 0;
            socklen_t socket_error_len = sizeof(socket_error);
            connected = getsockopt(fd, SOL_SOCKET, SO_ERROR, &socket_error, &socket_error_len) == 0 &&
                        socket_error == 0;
            if (!connected && socket_error != 0) errno = socket_error;
        }
        if (connected) break;
        if (fd >= 0) { close(fd); fd = -1; }
    }
    freeaddrinfo(results);
    if (fd < 0) {
        free(host_port);
        snprintf(error, error_cap, errno == ETIMEDOUT ? "HTTP request timed out" : "HTTP connection failed");
        return 0;
    }
    rt_http_set_socket_timeout(fd, deadline_ms);
    const char* request_target = target ? target : "/";
    char* query_target = NULL;
    if (request_target[0] == '?' || request_target[0] == '#') {
        query_target = (char*)malloc(strlen(request_target) + 2);
        if (!query_target) { close(fd); free(host_port); snprintf(error, error_cap, "out of memory"); return 0; }
        query_target[0] = '/'; strcpy(query_target + 1, request_target); request_target = query_target;
    }
    char* request = NULL; size_t request_len = 0, request_cap = 0; char line[256];
    int line_len = snprintf(line, sizeof(line), "%s %s HTTP/1.1\r\nHost: %s\r\nConnection: close\r\n",
                            method, request_target, host_port);
    int ok = line_len > 0 && (size_t)line_len < sizeof(line) &&
             rt_http_append(&request, &request_len, &request_cap, line, (size_t)line_len);
    free(query_target);
    if (ok && headers) {
        for (int64_t i = 0; i < headers->len; i++) {
            RtCoreString* header = rt_core_as_string(((int64_t*)headers->data)[i]);
            if (!header || memchr(header->data, '\r', header->len) || memchr(header->data, '\n', header->len)) continue;
            ok = rt_http_append(&request, &request_len, &request_cap, header->data, header->len) &&
                 rt_http_append(&request, &request_len, &request_cap, "\r\n", 2);
            if (!ok) break;
        }
    }
    if (ok && !rt_http_has_header(request, request_len, "Content-Length")) {
        line_len = snprintf(line, sizeof(line), "Content-Length: %zu\r\n", body_len);
        ok = line_len > 0 && (size_t)line_len < sizeof(line) &&
             rt_http_append(&request, &request_len, &request_cap, line, (size_t)line_len);
    }
    ok = ok && rt_http_append(&request, &request_len, &request_cap, "\r\n", 2);
    if (ok) ok = rt_http_send_all(fd, request, request_len, deadline_ms) &&
                 rt_http_send_all(fd, body, body_len, deadline_ms);
    free(request); free(host_port);
    if (!ok) {
        close(fd);
        snprintf(error, error_cap, errno == ETIMEDOUT ? "HTTP request timed out" : "HTTP request write failed");
        return 0;
    }
    size_t received = 0, capacity = 8192;
    uint8_t* response = (uint8_t*)malloc(capacity + 1);
    if (!response) { close(fd); snprintf(error, error_cap, "out of memory"); return 0; }
    for (;;) {
        if (received == capacity) {
            if (capacity >= 64 * 1024 * 1024) { free(response); close(fd); snprintf(error, error_cap, "HTTP response too large"); return 0; }
            capacity *= 2; uint8_t* grown = (uint8_t*)realloc(response, capacity + 1);
            if (!grown) { free(response); close(fd); snprintf(error, error_cap, "out of memory"); return 0; }
            response = grown;
        }
        if (!rt_http_wait_fd(fd, POLLIN, deadline_ms)) {
            free(response); close(fd); snprintf(error, error_cap, "HTTP request timed out"); return 0;
        }
        ssize_t n = recv(fd, response + received, capacity - received, 0);
        if (n < 0 && errno == EINTR) continue;
        if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) continue;
        if (n < 0) { free(response); close(fd); snprintf(error, error_cap, "HTTP response read failed"); return 0; }
        if (n == 0) break;
        received += (size_t)n;
    }
    close(fd); response[received] = '\0';
    const char* header_end = rt_http_header_end(response, received);
    if (!header_end) { free(response); snprintf(error, error_cap, "invalid HTTP response"); return 0; }
    int status = 0;
    if (sscanf((const char*)response, "HTTP/%*s %d", &status) != 1) {
        free(response); snprintf(error, error_cap, "invalid HTTP status"); return 0;
    }
    const char* header_start = strchr((const char*)response, '\n');
    if (!header_start || header_start >= header_end) { free(response); snprintf(error, error_cap, "invalid HTTP headers"); return 0; }
    header_start++; size_t header_len = (size_t)(header_end - header_start);
    const uint8_t* payload = (const uint8_t*)header_end + 4;
    size_t payload_len = received - (size_t)(payload - response);
    if (rt_http_has_header(header_start, header_len, "Transfer-Encoding") && strcasestr(header_start, "chunked")) {
        uint8_t* decoded = NULL; size_t decoded_len = 0;
        if (!rt_http_decode_chunked(payload, payload_len, &decoded, &decoded_len)) {
            free(response); snprintf(error, error_cap, "invalid chunked HTTP response"); return 0;
        }
        free(response); response = decoded; payload = response; payload_len = decoded_len;
    } else {
        int64_t declared = rt_http_content_length(header_start, header_len);
        if (declared >= 0 && (uint64_t)declared < payload_len) payload_len = (size_t)declared;
        memmove(response, payload, payload_len); payload = response;
    }
    *status_out = status; *body_out = response; *body_len_out = payload_len; return 1;
}
#endif

int64_t rt_http_get(int64_t url_value) {
    RtCoreString* url = rt_core_as_string(url_value);
    if (!url) return rt_http_tuple(-1, NULL, 0, "invalid HTTP URL text argument");
#if defined(_WIN32)
    return rt_http_tuple(-1, NULL, 0, "native HTTP is unavailable on Windows core runtime");
#else
    int64_t status = -1; uint8_t* body = NULL; size_t body_len = 0; char error[160] = {0};
    int ok = rt_http_perform("GET", url->data, NULL, NULL, 0, 0,
                             &status, &body, &body_len, error, sizeof(error));
    int64_t result = ok ? rt_http_tuple(status, body, body_len, "")
                        : rt_http_tuple(-1, NULL, 0, error);
    free(body); return result;
#endif
}

static int64_t rt_http_request_with_timeout(int64_t method_value, int64_t url_value,
                                            int64_t headers_value, int64_t body_value,
                                            int64_t timeout_ms) {
    RtCoreString* method = rt_core_as_string(method_value);
    RtCoreString* url = rt_core_as_string(url_value);
    RtCoreString* body = rt_core_as_string(body_value);
    if (!method || !url) return rt_http_tuple(-1, NULL, 0, "invalid HTTP text argument");
#if defined(_WIN32)
    return rt_http_tuple(-1, NULL, 0, "native HTTP is unavailable on Windows core runtime");
#else
    int64_t status = -1; uint8_t* response = NULL; size_t response_len = 0; char error[160] = {0};
    int ok = rt_http_perform(method->data, url->data, rt_core_as_array(headers_value),
                             body ? (const uint8_t*)body->data : NULL, body ? (size_t)body->len : 0,
                             timeout_ms,
                             &status, &response, &response_len, error, sizeof(error));
    int64_t result = ok ? rt_http_tuple(status, response, response_len, "")
                        : rt_http_tuple(-1, NULL, 0, error);
    free(response); return result;
#endif
}

int64_t rt_http_request(int64_t method_value, int64_t url_value, int64_t headers_value,
                        int64_t body_value) {
    return rt_http_request_with_timeout(method_value, url_value, headers_value, body_value, 0);
}

int64_t rt_http_client_request(int64_t client, int64_t method, int64_t url,
                               int64_t headers, int64_t body) {
    int64_t timeout_ms = 0;
    if (!rt_http_client_timeout(client, &timeout_ms)) {
        return rt_http_tuple(-1, NULL, 0, "invalid HTTP client");
    }
    return rt_http_request_with_timeout(method, url, headers, body, timeout_ms);
}

int64_t rt_http_download(int64_t url_value, int64_t output_path_value) {
    RtCoreString* url = rt_core_as_string(url_value);
    RtCoreString* output_path = rt_core_as_string(output_path_value);
    if (!url || !output_path) return rt_http_download_tuple(-1, 0, "invalid HTTP download text argument");
#if defined(_WIN32)
    return rt_http_download_tuple(-1, 0, "native HTTP is unavailable on Windows core runtime");
#else
    int64_t status = -1; uint8_t* body = NULL; size_t body_len = 0; char error[160] = {0};
    int ok = rt_http_perform("GET", url->data, NULL, NULL, 0, 0,
                             &status, &body, &body_len, error, sizeof(error));
    if (ok) {
        FILE* file = fopen(output_path->data, "wb");
        if (!file) {
            ok = 0; snprintf(error, sizeof(error), "HTTP download write failed");
        } else {
            size_t written = fwrite(body, 1, body_len, file);
            int closed = fclose(file) == 0;
            if (written != body_len || !closed) {
                ok = 0; snprintf(error, sizeof(error), "HTTP download write failed");
            }
        }
    }
    int64_t result = ok ? rt_http_download_tuple(status, body_len, "")
                        : rt_http_download_tuple(-1, 0, error);
    free(body); return result;
#endif
}

static void rt_glyph_pattern(uint8_t ch, uint8_t out[7]) {
    static const uint8_t upper[26][7] = {
        {14,17,17,31,17,17,17}, {30,17,17,30,17,17,30}, {15,16,16,16,16,16,15},
        {30,17,17,17,17,17,30}, {31,16,16,30,16,16,31}, {31,16,16,30,16,16,16},
        {15,16,16,23,17,17,15}, {17,17,17,31,17,17,17}, {31,4,4,4,4,4,31},
        {1,1,1,1,17,17,14}, {17,18,20,24,20,18,17}, {16,16,16,16,16,16,31},
        {17,27,21,21,17,17,17}, {17,25,21,19,17,17,17}, {14,17,17,17,17,17,14},
        {30,17,17,30,16,16,16}, {14,17,17,17,21,18,13}, {30,17,17,30,20,18,17},
        {15,16,16,14,1,1,30}, {31,4,4,4,4,4,4}, {17,17,17,17,17,17,14},
        {17,17,17,17,17,10,4}, {17,17,21,21,21,21,10}, {17,17,10,4,10,17,17},
        {17,17,10,4,4,4,4}, {31,1,2,4,8,16,31},
    };
    static const uint8_t digits[10][7] = {
        {14,17,19,21,25,17,14}, {4,12,4,4,4,4,14}, {14,17,1,2,4,8,31},
        {30,1,1,14,1,1,30}, {2,6,10,18,31,2,2}, {31,16,16,30,1,1,30},
        {14,16,16,30,17,17,14}, {31,1,2,4,8,8,8}, {14,17,17,14,17,17,14},
        {14,17,17,15,1,1,14},
    };
    if (ch >= 'a' && ch <= 'z') ch = (uint8_t)(ch - ('a' - 'A'));
    if (ch >= 'A' && ch <= 'Z') memcpy(out, upper[ch - 'A'], 7);
    else if (ch >= '0' && ch <= '9') memcpy(out, digits[ch - '0'], 7);
    else {
        switch (ch) {
            case ':': { const uint8_t p[7] = {0,4,4,0,4,4,0}; memcpy(out,p,7); break; }
            case '.': { const uint8_t p[7] = {0,0,0,0,0,12,12}; memcpy(out,p,7); break; }
            case '/': { const uint8_t p[7] = {1,2,2,4,8,8,16}; memcpy(out,p,7); break; }
            case '-': { const uint8_t p[7] = {0,0,0,31,0,0,0}; memcpy(out,p,7); break; }
            case '_': { const uint8_t p[7] = {0,0,0,0,0,0,31}; memcpy(out,p,7); break; }
            case '$': { const uint8_t p[7] = {4,15,20,14,5,30,4}; memcpy(out,p,7); break; }
            case '>': { const uint8_t p[7] = {16,8,4,2,4,8,16}; memcpy(out,p,7); break; }
            case '<': { const uint8_t p[7] = {1,2,4,8,4,2,1}; memcpy(out,p,7); break; }
            case '=': { const uint8_t p[7] = {0,0,31,0,31,0,0}; memcpy(out,p,7); break; }
            case '?': { const uint8_t p[7] = {14,17,1,2,4,0,4}; memcpy(out,p,7); break; }
            case ' ': memset(out, 0, 7); break;
            default: { const uint8_t p[7] = {31,1,2,4,4,0,4}; memcpy(out,p,7); break; }
        }
    }
}

int64_t rt_gui_get_glyph_8x16(int32_t codepoint) {
    SplArray* result = rt_byte_array_new(16);
    RtCoreArray* array = rt_core_array_ptr(result);
    if (!array || !array->data) return (int64_t)(uintptr_t)result;
    memset(array->data, 0, 16);
    if (codepoint <= 0 || codepoint == 32) { array->len = 16; return (int64_t)(uintptr_t)result; }
    uint8_t pattern[7];
    rt_glyph_pattern((codepoint >= 0x20 && codepoint <= 0x7e) ? (uint8_t)codepoint : '?', pattern);
    for (int row = 0; row < 7; row++) {
        uint8_t expanded = 0;
        for (int col = 0; col < 5; col++) if (pattern[row] & (uint8_t)(16 >> col)) expanded |= (uint8_t)(64 >> col);
        ((uint8_t*)array->data)[1 + row * 2] = expanded;
        ((uint8_t*)array->data)[2 + row * 2] = expanded;
    }
    array->len = 16;
    return (int64_t)(uintptr_t)result;
}

int64_t rt_file_size(const uint8_t* path_ptr, uint64_t path_len) {
    char path[RT_TEXT_PATH_MAX];
    if (!rt_text_arg_to_path(path_ptr, path_len, path, sizeof(path))) return -1;
    struct stat st;
    if (stat(path, &st) != 0) return -1;
    return (int64_t)st.st_size;
}

static char* rt_core_text_arg_to_cstr(const uint8_t* ptr, uint64_t len) {
    if (!ptr && len != 0) return NULL;
    char* out = (char*)malloc((size_t)len + 1);
    if (!out) return NULL;
    if (len != 0) memcpy(out, ptr, (size_t)len);
    out[len] = '\0';
    return out;
}

int64_t rt_path_join(
    const uint8_t* left,
    uint64_t left_len,
    const uint8_t* right,
    uint64_t right_len
) {
    if (!left) return rt_string_new(NULL, 0);
    if (left_len > SIZE_MAX || right_len > SIZE_MAX) return rt_core_nil();
    if (!right || right_len == 0) return rt_string_new(left, left_len);
    if (right[0] == '/' || left_len == 0) return rt_string_new(right, right_len);

    uint64_t separator_len = left[left_len - 1] == '/' ? 0 : 1;
    if (separator_len > SIZE_MAX - right_len) return rt_core_nil();
    if (left_len > SIZE_MAX - right_len - separator_len) return rt_core_nil();
    size_t joined_len = (size_t)(left_len + right_len + separator_len);
    uint8_t* joined = (uint8_t*)malloc(joined_len);
    if (!joined) return rt_core_nil();
    memcpy(joined, left, (size_t)left_len);
    if (separator_len) joined[left_len] = '/';
    memcpy(joined + left_len + separator_len, right, (size_t)right_len);
    int64_t result = rt_string_new(joined, joined_len);
    free(joined);
    return result;
}

static int64_t rt_env_get_cstr(const char* key) {
    if (!key) return rt_core_nil();
    const char* value = getenv(key);
    if (!value) return rt_core_nil();
    return rt_string_new((const uint8_t*)value, (uint64_t)strlen(value));
}

int64_t rt_env_get(const uint8_t* key_ptr, uint64_t key_len) {
    char* key = rt_core_text_arg_to_cstr(key_ptr, key_len);
    int64_t result = rt_env_get_cstr(key);
    free(key);
    return result;
}

int64_t rt_env_get_value(int64_t key) {
    return rt_env_get_cstr(rt_interp_cstr(key));
}

static atomic_flag rt_lexer_source_lock = ATOMIC_FLAG_INIT;
static uint8_t* rt_lexer_source_bytes = NULL;
static uint64_t rt_lexer_source_length = 0;

static void rt_lexer_source_acquire(void) {
    while (atomic_flag_test_and_set_explicit(&rt_lexer_source_lock, memory_order_acquire)) {}
}

static void rt_lexer_source_release(void) {
    atomic_flag_clear_explicit(&rt_lexer_source_lock, memory_order_release);
}

bool rt_lexer_source_set(const uint8_t* source_ptr, uint64_t source_len) {
    if (!source_ptr && source_len != 0) return false;
    uint8_t* replacement = (uint8_t*)malloc((size_t)source_len + 1);
    if (!replacement) return false;
    if (source_len != 0) memcpy(replacement, source_ptr, (size_t)source_len);
    replacement[source_len] = 0;
    rt_lexer_source_acquire();
    uint8_t* previous = rt_lexer_source_bytes;
    rt_lexer_source_bytes = replacement;
    rt_lexer_source_length = source_len;
    rt_lexer_source_release();
    free(previous);
    return true;
}

static bool rt_lexer_source_char_to_byte(uint64_t target, uint64_t* byte_offset) {
    uint64_t chars = 0;
    for (uint64_t i = 0; i < rt_lexer_source_length; i++) {
        if ((rt_lexer_source_bytes[i] & 0xC0) != 0x80) {
            if (chars == target) {
                *byte_offset = i;
                return true;
            }
            chars++;
        }
    }
    if (chars == target) {
        *byte_offset = rt_lexer_source_length;
        return true;
    }
    return false;
}

int64_t rt_lexer_source_slice(int64_t start, int64_t end) {
    if (start < 0 || end < start) return rt_core_nil();
    rt_lexer_source_acquire();
    uint64_t ustart;
    uint64_t uend;
    if (!rt_lexer_source_char_to_byte((uint64_t)start, &ustart) ||
        !rt_lexer_source_char_to_byte((uint64_t)end, &uend)) {
        rt_lexer_source_release();
        return rt_core_nil();
    }
    const uint8_t* bytes = rt_lexer_source_bytes ? rt_lexer_source_bytes + ustart : (const uint8_t*)"";
    int64_t result = rt_string_new(bytes, uend - ustart);
    rt_lexer_source_release();
    return result;
}

int64_t rt_env_get_i64(const uint8_t* key_ptr, uint64_t key_len, int64_t default_value) {
    char* key = rt_core_text_arg_to_cstr(key_ptr, key_len);
    if (!key) return default_value;
    const char* value = getenv(key);
    if (!value || value[0] == '\0') {
        free(key);
        return default_value;
    }
    char* end = NULL;
    long long parsed = strtoll(value, &end, 10);
    free(key);
    return end == value ? default_value : (int64_t)parsed;
}

bool rt_env_set(const uint8_t* key_ptr, uint64_t key_len, const uint8_t* value_ptr, uint64_t value_len) {
    char* key = rt_core_text_arg_to_cstr(key_ptr, key_len);
    char* value = rt_core_text_arg_to_cstr(value_ptr, value_len);
    if (!key || !value) {
        free(key);
        free(value);
        return false;
    }
#if defined(_WIN32)
    bool ok = _putenv_s(key, value) == 0;
#else
    bool ok = setenv(key, value, 1) == 0;
#endif
    free(key);
    free(value);
    return ok;
}

/* rt_env_remove — delete a variable from the environment.
 *
 * Had no C definition anywhere (only the interpreter-side Rust in
 * interpreter_extern/system.rs, which is not an extern "C" symbol), so the
 * SimpleOS cross-link could not resolve it. Signature is the (ptr,len) text
 * ABI, matching rt_env_set directly above: &[I64,I64] -> &[I8]. */
int8_t rt_env_remove(const uint8_t* key_ptr, uint64_t key_len) {
    char* key = rt_core_text_arg_to_cstr(key_ptr, key_len);
    if (!key) return 0;
#if defined(_WIN32)
    /* Windows deletes a variable by assigning it an empty value. */
    bool ok = _putenv_s(key, "") == 0;
#else
    bool ok = unsetenv(key) == 0;
#endif
    free(key);
    return ok ? 1 : 0;
}

/* rt_file_write, rt_file_copy, rt_file_size, rt_file_stat, rt_file_append
 * are still defined in runtime.c only — add them here when needed. */

static char* rt_core_string_to_cpath(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) return NULL;
    char* out = (char*)malloc((size_t)s->len + 1);
    if (!out) return NULL;
    if (s->len > 0) memcpy(out, s->data, (size_t)s->len);
    out[s->len] = '\0';
    return out;
}

static const uint8_t* rt_core_string_bytes(int64_t value, uint64_t* len_out) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) {
        *len_out = 0;
        return NULL;
    }
    *len_out = s->len;
    return (const uint8_t*)s->data;
}

int64_t rt_file_atomic_write(int64_t path_value, int64_t content_value) {
    static atomic_uint_fast64_t sequence = 0;
    RtCoreString* path_string = rt_core_as_string(path_value);
    RtCoreString* content_string = rt_core_as_string(content_value);
    if (!path_string || !content_string || path_string->len == 0 ||
        memchr(path_string->data, '\0', (size_t)path_string->len) != NULL) return 0;

    char* path = rt_core_string_to_cpath(path_value);
    if (!path) return 0;
#if !defined(_WIN32)
    struct stat existing_stat;
    int preserve_mode = stat(path, &existing_stat) == 0;
#endif
    char* parent = spl_strdup(path);
    if (!parent) {
        free(path);
        return 0;
    }
    char* slash = strrchr(parent, '/');
#if defined(_WIN32)
    char* backslash = strrchr(parent, '\\');
    if (!slash || (backslash && backslash > slash)) slash = backslash;
#endif
    if (slash) {
        if (slash == parent || (slash == parent + 2 && parent[1] == ':')) slash[1] = '\0';
        else *slash = '\0';
        /* C-internal caller: `parent` IS a real NUL-terminated C string, so it
         * must be passed through the (ptr, len) `text` extern ABI explicitly. */
        if (!rt_dir_exists((const uint8_t*)parent, (uint64_t)strlen(parent)) &&
            !rt_dir_create_cpath(parent, true)) {
            free(parent);
            free(path);
            return 0;
        }
    }
    free(parent);
    size_t path_len = strlen(path);
    char* temp_path = (char*)malloc(path_len + 64);
    if (!temp_path) {
        free(path);
        return 0;
    }
    int fd = -1;
    for (int attempt = 0; attempt < 16 && fd < 0; attempt++) {
#if defined(_WIN32)
        int temp_len = snprintf(temp_path, path_len + 64, "%s.tmp.%lu.%llu", path,
                                (unsigned long)GetCurrentProcessId(),
                                (unsigned long long)atomic_fetch_add(&sequence, 1));
        if (temp_len >= 0 && (size_t)temp_len < path_len + 64)
            fd = _open(temp_path, _O_WRONLY | _O_CREAT | _O_EXCL | _O_BINARY, _S_IREAD | _S_IWRITE);
#else
        int temp_len = snprintf(temp_path, path_len + 64, "%s.tmp.%ld.%llu", path,
                                (long)getpid(), (unsigned long long)atomic_fetch_add(&sequence, 1));
        if (temp_len >= 0 && (size_t)temp_len < path_len + 64)
            fd = open(temp_path, O_WRONLY | O_CREAT | O_EXCL, 0600);
#endif
        if (fd < 0 && errno != EEXIST) break;
    }
#if defined(_WIN32)
    FILE* file = fd < 0 ? NULL : _fdopen(fd, "wb");
#else
    FILE* file = fd < 0 ? NULL : fdopen(fd, "wb");
#endif
    int created = fd >= 0;
    int ok = file != NULL;
    if (ok) ok = fwrite(content_string->data, 1, (size_t)content_string->len, file) == (size_t)content_string->len;
    if (ok) ok = fflush(file) == 0;
#if !defined(_WIN32)
    if (ok && preserve_mode) ok = fchmod(fd, existing_stat.st_mode & 07777) == 0;
#endif
#if defined(_WIN32)
    if (ok) ok = _commit(fd) == 0;
#else
    if (ok) ok = fsync(fd) == 0;
#endif
    if (file && fclose(file) != 0) ok = 0;
    else if (!file && fd >= 0) {
#if defined(_WIN32)
        _close(fd);
#else
        close(fd);
#endif
    }
#if defined(_WIN32)
    if (ok) ok = MoveFileExA(temp_path, path, MOVEFILE_REPLACE_EXISTING | MOVEFILE_WRITE_THROUGH) != 0;
#else
    if (ok) ok = rename(temp_path, path) == 0;
#endif
    if (created && !ok) remove(temp_path);
    free(temp_path);
    free(path);
    return ok ? 1 : 0;
}

static ssize_t rt_file_read_at_fd(int fd, void* buffer, size_t size, int64_t offset) {
#if defined(_WIN32)
    if (_lseeki64(fd, offset, SEEK_SET) < 0) return -1;
    return (ssize_t)read(fd, buffer, (unsigned int)size);
#else
    return pread(fd, buffer, size, (off_t)offset);
#endif
}

static ssize_t rt_file_write_at_fd(int fd, const void* data, size_t size, int64_t offset) {
#if defined(_WIN32)
    if (_lseeki64(fd, offset, SEEK_SET) < 0) return -1;
    return (ssize_t)write(fd, data, (unsigned int)size);
#else
    return pwrite(fd, data, size, (off_t)offset);
#endif
}

/* SFFI_LEGACY_UNSAFE: mixed static/heap ownership. Kept only for binary
 * compatibility; safe Simple code binds rt_file_read_text_at_checked. */
const char* rt_file_read_text_at(const char* path_value, int64_t offset, int64_t size) {
    char* path = rt_core_string_to_cpath((int64_t)(uintptr_t)path_value);
    if (!path || offset < 0) {
        if (path) free(path);
        return "";
    }
    if (size <= 0) {
        free(path);
        return "";
    }

    int fd = open(path, O_RDONLY);
    free(path);
    if (fd < 0) return "";

    char* buffer = (char*)malloc((size_t)size + 1);
    if (!buffer) {
        close(fd);
        return "";
    }

    ssize_t bytes_read = rt_file_read_at_fd(fd, buffer, (size_t)size, offset);
    close(fd);
    if (bytes_read < 0) {
        free(buffer);
        return "";
    }

    buffer[bytes_read] = '\0';
    return buffer;
}

int64_t rt_file_read_text_at_checked(int64_t path_value, int64_t offset, int64_t size) {
    char* path = rt_core_string_to_cpath(path_value);
    if (!path || offset < 0 || size < 0 || (uint64_t)size > SIZE_MAX) {
        if (path) free(path);
        return 0;
    }
    if (size == 0) {
        free(path);
        return rt_string_new(NULL, 0);
    }

    int fd = open(path, O_RDONLY);
    free(path);
    if (fd < 0) return 0;

    uint8_t* buffer = (uint8_t*)malloc((size_t)size);
    if (!buffer) {
        close(fd);
        return 0;
    }
    ssize_t bytes_read = rt_file_read_at_fd(fd, buffer, (size_t)size, offset);
    close(fd);
    if (bytes_read < 0) {
        free(buffer);
        return 0;
    }
    int64_t result = rt_string_new(buffer, (uint64_t)bytes_read);
    free(buffer);
    return result;
}

int64_t rt_file_write_text_at(int64_t path_value, int64_t offset_value, int64_t data_value) {
    char* path = rt_core_string_to_cpath(path_value);
    uint64_t data_len = 0;
    const uint8_t* data = rt_core_string_bytes(data_value, &data_len);
    int64_t offset = rt_core_is_int(offset_value) ? rt_core_as_int(offset_value) : offset_value;
    if (!path || !data || offset < 0) {
        if (path) free(path);
        return -1;
    }
    if (data_len == 0) {
        free(path);
        return 0;
    }

    int fd = open(path, O_WRONLY | O_CREAT, 0644);
    free(path);
    if (fd < 0) return -1;

    ssize_t bytes_written = rt_file_write_at_fd(fd, data, (size_t)data_len, offset);
    close(fd);
    return (int64_t)bytes_written;
}

/* NOTE (2026-08-10, rt_extern_abi_divergence_family): this is a stdio FILE*
 * helper, NOT the compiler's rt_file_open. The compiler declares
 * `i32 rt_file_open(const uint8_t* path, uint64_t path_len, i32 mode)` and the
 * canonical implementation is
 * src/compiler_rust/runtime/src/value/sffi/file_io/descriptor.rs. Sharing the
 * name meant `-z muldefs` could hand callers this fopen() wrapper instead:
 * it would read `path` as a NUL-terminated string (a Simple `text` is not),
 * treat the LENGTH word as a `const char*` mode string, and return a FILE*
 * where an fd was expected. Renamed so the two can never collide again. Do
 * not rename it back. */
void* rt_file_open_stream(const char* path, const char* mode) {
    if (!path || !mode) return NULL;
    return (void*)fopen(path, mode);
}

/* Two `text` arguments -> FOUR machine words; runtime_sffi.rs:1881 declares
 * &[I64, I64, I64, I64]. The old two-parameter form read both paths past
 * their ends -- and a rename() with a corrupted destination does not fail
 * safe, it moves the file somewhere unintended. */
int rt_file_move(const uint8_t* src_ptr, uint64_t src_len,
                 const uint8_t* dst_ptr, uint64_t dst_len) {
    char src[RT_TEXT_PATH_MAX];
    char dst[RT_TEXT_PATH_MAX];
    if (!rt_text_arg_to_path(src_ptr, src_len, src, sizeof(src))) return 0;
    if (!rt_text_arg_to_path(dst_ptr, dst_len, dst, sizeof(dst))) return 0;
    return rename(src, dst) == 0 ? 1 : 0;
}

/* () -> RuntimeValue, per runtime_sffi.rs:1773 `RuntimeFuncSpec::new(
 * "rt_env_cwd", &[], &[I64])`.  The canonical Rust definition
 * (sffi/env_process.rs:282) returns a RuntimeValue too.  This copy used to
 * return the raw malloc'd `char*` out of rt_getcwd(); the caller decoded that
 * heap address as a tagged value and the runtime's own handle validator
 * rejected it ("probable compiler/FFI ABI mismatch"), so a perfectly good cwd
 * read back as garbage/empty -- see the rt_file_read_text sibling. */
int64_t rt_env_cwd(void) {
    char* cwd = rt_getcwd();
    /* RT_NIL == 3 (TAG_SPECIAL, payload 0); == RuntimeValue::NIL. */
    if (!cwd) return 3;
    int64_t result = rt_string_new((const uint8_t*)cwd, (uint64_t)strlen(cwd));
    free(cwd);
    return result;
}

/* () -> RuntimeValue, per runtime_sffi.rs:1791.  Used to return a pointer into
 * .rodata: not merely untagged but not even 8-aligned, so the returned word
 * carried a nonsense tag (observed tag=4). */
int64_t rt_platform_name(void) {
#if defined(_WIN32)
    const char* name = "windows";
#elif defined(__APPLE__)
    const char* name = "macos";
#elif defined(__FreeBSD__)
    const char* name = "freebsd";
#elif defined(__linux__)
    const char* name = "linux";
#elif defined(__illumos__)
    const char* name = "illumos";
#elif defined(__sun) && defined(__SVR4)
    const char* name = "solaris";
#else
    const char* name = "unknown";
#endif
    return rt_string_new((const uint8_t*)name, (uint64_t)strlen(name));
}

static int rt_core_file_write_data(
    const uint8_t* path_ptr,
    uint64_t path_len,
    const uint8_t* data,
    uint64_t data_len,
    const char* mode
) {
    if (!path_ptr || (!data && data_len != 0) || path_len > SIZE_MAX - 1) return 0;
    char* path = rt_core_text_arg_to_cstr(path_ptr, path_len);
    if (!path) return 0;
    FILE* f = fopen(path, mode);
    free(path);
    if (!f) return 0;
    size_t written = fwrite(data, 1, (size_t)data_len, f);
    fclose(f);
    return written == (size_t)data_len ? 1 : 0;
}

int rt_file_write_text(const uint8_t* path, uint64_t path_len, const uint8_t* content, uint64_t content_len) {
    return rt_core_file_write_data(path, path_len, content, content_len, "wb");
}

int rt_file_append_text(const uint8_t* path, uint64_t path_len, const uint8_t* content, uint64_t content_len) {
    return rt_core_file_write_data(path, path_len, content, content_len, "ab");
}

static int rt_core_mkdir_one(const char* path) {
    if (!path || !*path) return 0;
#if defined(_WIN32)
    if (mkdir(path) == 0) return 1;
#else
    if (mkdir(path, 0777) == 0) return 1;
#endif
    return rt_is_dir(path) ? 1 : 0;
}

/* C-string worker for rt_dir_create_all / rt_mkdir_p. */
static int rt_dir_create_all_cpath(const char* path) {
    if (!path || !*path) return 0;
    char* copy = spl_strdup(path);
    if (!copy) return 0;

    char* p = copy;
    if (p[0] == '/') p++;
    for (; *p; p++) {
        if (*p == '/') {
            *p = '\0';
            if (!rt_core_mkdir_one(copy)) {
                free(copy);
                return 0;
            }
            *p = '/';
        }
    }

    int ok = rt_core_mkdir_one(copy);
    free(copy);
    return ok;
}

int rt_dir_create_all(const uint8_t* path_ptr, uint64_t path_len) {
    char path[RT_TEXT_PATH_MAX];
    if (!rt_text_arg_to_path(path_ptr, path_len, path, sizeof(path))) return 0;
    return rt_dir_create_all_cpath(path);
}

/* rt_mkdir_p has no RuntimeFuncSpec -- the compiler never calls it -- so it
 * stays a C-string helper over the same worker. */
int rt_mkdir_p(const char* path) {
    return rt_dir_create_all_cpath(path);
}

bool rt_dir_create(const uint8_t* path_ptr, uint64_t path_len, bool recursive) {
    char path[RT_TEXT_PATH_MAX];
    if (!rt_text_arg_to_path(path_ptr, path_len, path, sizeof(path))) return false;
    return rt_dir_create_cpath(path, recursive);
}

const char* lib__nogc_sync_mut__debug__remote__session_model__DebugExecutionMode_dot_to_string(int64_t value) {
    switch (value) {
        case 1: return "rtl_sim";
        case 2: return "qemu_stub";
        default: return "hw";
    }
}

const char* lib__nogc_sync_mut__debug__remote__session_model__DebugTransportKind_dot_to_string(int64_t value) {
    switch (value) {
        case 1: return "openocd_remote_bitbang";
        case 2: return "intel_jtagd";
        case 3: return "trace32_native";
        case 4: return "trace32_gdb";
        case 5: return "gdb_remote";
        default: return "openocd_jtag";
    }
}

const char* lib__nogc_sync_mut__debug__remote__types__Architecture_dot_to_string(int64_t value) {
    switch (value) {
        case 1: return "arm64";
        case 2: return "riscv32";
        case 3: return "riscv64";
        case 4: return "x86";
        case 5: return "x86_64";
        default: return "arm32";
    }
}

static char* rt_core_shell_quote(const char* s) {
    if (!s) return spl_strdup("''");
    size_t extra = 2;
    for (const char* p = s; *p; p++) {
        extra += (*p == '\'') ? 4 : 1;
    }
    char* out = (char*)malloc(extra + 1);
    if (!out) return spl_strdup("''");
    char* w = out;
    *w++ = '\'';
    for (const char* p = s; *p; p++) {
        if (*p == '\'') {
            memcpy(w, "'\\''", 4);
            w += 4;
        } else {
            *w++ = *p;
        }
    }
    *w++ = '\'';
    *w = '\0';
    return out;
}

/* (cmd_ptr, cmd_len, args) -> RuntimeValue (array), per runtime_sffi.rs:1419.
 *
 * The BODY was already correct: the result is built with rt_array_new /
 * rt_array_push / rt_string_new, so it carries RT_VALUE_TAG_HEAP and is owned
 * by the rt_core registry -- exactly what the compiler decodes. Verified in all
 * three C link orders: raw=0x...2a1, tag=1, array_len=3. cmd_len is honoured
 * and forwarded, so the (ptr, len) parameter ABI is respected too. Only the C
 * RETURN TYPE was spelled `SplArray*` where the compiler and the canonical Rust
 * definition (sffi/env_process.rs:585 -> RuntimeValue) say I64.
 *
 * The body is kept as rt_process_run_array() because two C-internal callers
 * (rt_process_run_tuple, and rt_process_result_to_tuple's contract) want the
 * SplArray* form; rt_process_run is now the thin entry point that states the
 * declared result type. Same worker/entry-point split the (ptr, len) parameter
 * fixes used for rt_dir_create_cpath et al. */
static SplArray* rt_process_run_array(const char* cmd, uint64_t cmd_len, SplArray* args) {
    SplArray* result = rt_array_new(3);
    if (!cmd || cmd_len == 0) {
        rt_array_push(result, rt_string_new((const uint8_t*)"", 0));
        rt_array_push(result, rt_string_new((const uint8_t*)"missing command", 15));
        rt_array_push(result, rt_value_int(-1));
        return result;
    }

    char* cmd_c = (char*)malloc((size_t)cmd_len + 1);
    if (!cmd_c) {
        rt_array_push(result, rt_string_new((const uint8_t*)"", 0));
        rt_array_push(result, rt_string_new((const uint8_t*)"process spawn failed", 20));
        rt_array_push(result, rt_value_int(-1));
        return result;
    }
    memcpy(cmd_c, cmd, (size_t)cmd_len);
    cmd_c[cmd_len] = '\0';

    char* command = rt_core_shell_quote(cmd_c);
    free(cmd_c);
    int64_t argc = rt_array_len(args);
    for (int64_t i = 0; i < argc; i++) {
        int64_t arg = rt_array_get(args, i);
        const uint8_t* arg_data = rt_string_data(arg);
        const char* arg_s = arg_data ? (const char*)arg_data : "";
        char* quoted = rt_core_shell_quote(arg_s);
        size_t new_len = strlen(command) + strlen(quoted) + 2;
        char* joined = (char*)malloc(new_len);
        if (!joined) {
            free(quoted);
            continue;
        }
        snprintf(joined, new_len, "%s %s", command, quoted);
        free(command);
        free(quoted);
        command = joined;
    }

    char* redirected = spl_str_concat(command, " 2>/tmp/simple_core_process_run_stderr");
    FILE* pipe = popen(redirected ? redirected : command, "r");
    free(command);
    if (redirected) free(redirected);
    if (!pipe) {
        rt_array_push(result, rt_string_new((const uint8_t*)"", 0));
        rt_array_push(result, rt_string_new((const uint8_t*)"process spawn failed", 20));
        rt_array_push(result, rt_value_int(-1));
        return result;
    }

    size_t cap = 4096;
    size_t len = 0;
    char* stdout_buf = (char*)malloc(cap);
    if (!stdout_buf) stdout_buf = spl_strdup("");
    if (stdout_buf) stdout_buf[0] = '\0';
    char chunk[512];
    while (fgets(chunk, sizeof(chunk), pipe)) {
        size_t chunk_len = strlen(chunk);
        if (len + chunk_len + 1 > cap) {
            while (len + chunk_len + 1 > cap) cap *= 2;
            stdout_buf = (char*)realloc(stdout_buf, cap);
            if (!stdout_buf) break;
        }
        memcpy(stdout_buf + len, chunk, chunk_len);
        len += chunk_len;
        stdout_buf[len] = '\0';
    }
    int status = pclose(pipe);
    int exit_code = status == -1 ? -1 : (status >> 8);

    const char* stdout_text = stdout_buf ? stdout_buf : "";
    rt_array_push(result, rt_string_new((const uint8_t*)stdout_text, (uint64_t)strlen(stdout_text)));
    rt_array_push(result, rt_string_new((const uint8_t*)"", 0));
    rt_array_push(result, rt_value_int(exit_code));
    if (stdout_buf) free(stdout_buf);
    return result;
}

int64_t rt_process_run_inherit(const char* cmd, uint64_t cmd_len, SplArray* args) {
    if (!cmd || cmd_len == 0) return -1;
    char* command = (char*)malloc((size_t)cmd_len + 1);
    if (!command) return -1;
    memcpy(command, cmd, (size_t)cmd_len);
    command[cmd_len] = '\0';

    int64_t argc = rt_array_len(args);
    const char** argv = (const char**)calloc((size_t)argc, sizeof(char*));
    if (argc > 0 && !argv) {
        free(command);
        return -1;
    }
    for (int64_t i = 0; i < argc; i++) {
        const uint8_t* value = rt_string_data(rt_array_get(args, i));
        argv[i] = value ? (const char*)value : "";
    }
    int64_t pid = rt_process_spawn_async(command, argv, argc);
    int64_t code = pid <= 0 ? -1 : rt_process_wait(pid, 0);
    free(argv);
    free(command);
    return code;
}

/* Native-codegen tuple facades for the process externs.
 *
 * The pure-Simple LLVM backend emits extern calls with the .spl-declared
 * shape -- `rt_process_run_timeout(cmd: text, args: [text], timeout_ms: i64)
 * -> (text, text, i32)` -- i.e. cmd as ONE tagged-or-raw text value, and it
 * destructures the tuple result as a pointer to 3 native i64 words (the
 * rt_alloc'd word-block layout of aggregate_intrinsics.spl's Tuple case).
 * The C owners (rt_process_run_timeout in runtime_process.c, rt_process_run
 * above) use the seed ABI instead: cmd as a (ptr, len) pair and an SplArray*
 * result whose slot 2 is a TAGGED int (rt_value_int). Calling the seed-ABI
 * symbol directly from generated native code therefore misaligns every
 * argument after cmd and misreads the result (parity case
 * process_run_timeout: SIGSEGV). translate_call (core_codegen.spl) rewrites
 * the callee names to these facades on the native path; the seed-ABI symbols
 * stay untouched for seed-compiled callers. */
static int64_t* rt_process_result_to_tuple(SplArray* result) {
    int64_t* tuple = (int64_t*)rt_alloc(3 * (int64_t)sizeof(int64_t));
    if (!tuple) return NULL;
    tuple[0] = rt_array_get(result, 0);
    tuple[1] = rt_array_get(result, 1);
    /* slot 2 is always pushed via rt_value_int by both C owners: untag. */
    tuple[2] = rt_value_as_int(rt_array_get(result, 2));
    return tuple;
}

int64_t rt_process_run_inherit_value(int64_t cmd, SplArray* args) {
    const char* cmd_c = rt_interp_cstr(cmd);
    uint64_t cmd_len = cmd_c ? (uint64_t)strlen(cmd_c) : 0;
    return rt_process_run_inherit(cmd_c ? cmd_c : "", cmd_len, args);
}

int64_t rt_process_spawn_guarded_value(int64_t cmd, SplArray* args) {
    const char* command = rt_interp_cstr(cmd);
    if (!command) return -1;
    int64_t argc = rt_array_len(args);
    const char** argv = (const char**)calloc((size_t)argc + 1, sizeof(char*));
    if (!argv) return -1;
    for (int64_t i = 0; i < argc; i++) {
        const char* value = rt_interp_cstr(rt_array_get_text(args, i));
        argv[i] = value ? value : "";
    }
    int64_t pid = rt_process_spawn_guarded(command, argv, argc);
    free(argv);
    return pid;
}

int64_t rt_process_run(const char* cmd, uint64_t cmd_len, SplArray* args) {
    return (int64_t)(uintptr_t)rt_process_run_array(cmd, cmd_len, args);
}

int64_t* rt_process_run_tuple(int64_t cmd, SplArray* args) {
    const char* cmd_c = rt_interp_cstr(cmd);
    uint64_t cmd_len = cmd_c ? (uint64_t)strlen(cmd_c) : 0;
    return rt_process_result_to_tuple(rt_process_run_array(cmd_c ? cmd_c : "", cmd_len, args));
}

int64_t* rt_process_run_timeout_tuple(int64_t cmd, SplArray* args, int64_t timeout_ms) {
    const char* cmd_c = rt_interp_cstr(cmd);
    uint64_t cmd_len = cmd_c ? (uint64_t)strlen(cmd_c) : 0;
    // rt_process_run_timeout's declared return type is int64_t (RuntimeValue
    // ABI, see commit 072c6754e09 "state the RuntimeValue return type for
    // rt_process_run{,_timeout}"); it still returns an SplArray* handle
    // widened to an integer, exactly like rt_process_run above does at
    // `(int64_t)(uintptr_t)rt_process_run_array(...)`. This call site was left
    // uncast by that change, so -Wint-conversion made runtime_native.c fail to
    // compile -- which broke the LLVM native-link step of EVERY native-build,
    // for every program, including `print "x"`.
    return rt_process_result_to_tuple(
        (SplArray*)(uintptr_t)rt_process_run_timeout(cmd_c ? cmd_c : "", cmd_len, args, timeout_ms));
}

int64_t* rt_process_run_bounded_tuple(int64_t cmd, SplArray* args, int64_t timeout_ms,
                                      int64_t max_output_bytes) {
    const char* cmd_c = rt_interp_cstr(cmd);
    uint64_t cmd_len = cmd_c ? (uint64_t)strlen(cmd_c) : 0;
    return rt_process_result_to_tuple(rt_process_run_bounded(
        cmd_c ? cmd_c : "", cmd_len, args, timeout_ms, max_output_bytes));
}

int64_t rt_file_read_bytes(const uint8_t* path_ptr, uint64_t path_len) {
    if (!path_ptr || path_len > SIZE_MAX - 1) return 0;
    char* path = (char*)malloc((size_t)path_len + 1);
    if (!path) return 0;
    memcpy(path, path_ptr, (size_t)path_len);
    path[path_len] = '\0';

    FILE* f = fopen(path, "rb");
    free(path);
    if (!f) return 0;
    if (fseek(f, 0, SEEK_END) != 0) {
        fclose(f);
        return 0;
    }
    long file_len = ftell(f);
    if (file_len < 0 || fseek(f, 0, SEEK_SET) != 0) {
        fclose(f);
        return 0;
    }

    SplArray* result = rt_byte_array_new_len((uint64_t)file_len);
    RtCoreArray* array = rt_core_array_ptr(result);
    if (!array || (file_len > 0 && fread(array->data, 1, (size_t)file_len, f) != (size_t)file_len)) {
        fclose(f);
        return 0;
    }
    fclose(f);
    return (int64_t)(uintptr_t)result;
}

int64_t rt_file_read_all_text(int64_t path_tagged) {
    char* path = rt_core_string_to_cpath(path_tagged);
    if (!path) return rt_string_new(NULL, 0);
    char* content = spl_file_read(path);
    free(path);
    if (!content) return rt_string_new(NULL, 0);
    size_t len = strlen(content);
    int64_t result = rt_string_new((const uint8_t*)content, (uint64_t)len);
    free(content);
    return result;
}


int rt_file_write_bytes(const uint8_t* path_ptr, uint64_t path_len, const uint8_t* data, uint64_t len) {
    return rt_core_file_write_data(path_ptr, path_len, data, len, "wb");
}

/* IF-13 wave-4d: truncate (or zero-extend) `path` to exactly `size` bytes.
 * Used by SimpleOS disk-image bake to push the multi-MiB zero-fill into the
 * kernel rather than building a giant byte-array in the interpreter. */
int rt_file_truncate(const char* path, uint64_t size) {
    if (!path) return 0;
    int fd = open(path, O_WRONLY | O_CREAT, 0644);
    if (fd < 0) return 0;
    int rc = ftruncate(fd, (off_t)size);
    close(fd);
    return rc == 0 ? 1 : 0;
}

/* (ptr, len) -> RuntimeValue (byte array), per runtime_sffi.rs:1876.
 *
 * The BODY was already correct: rt_byte_array_new_len returns a value the
 * rt_core registry owns and that carries RT_VALUE_TAG_HEAP, which is exactly
 * what the compiler decodes -- verified in all three C link orders
 * (raw=0x...2a1, tag=1, array_len=5 for a 5-byte source). Only the C RETURN
 * TYPE was spelled `SplArray*` where the compiler and the canonical Rust
 * definition (sffi/file_io/file_ops.rs:1006 -> RuntimeValue) say I64, which is
 * what the extern ABI gate flagged. Spelling it int64_t makes the C signature
 * state what the function actually returns; it is not a behaviour change.
 * src/runtime/test/rt_browser_http_job_provider_selfcheck.c:17 already
 * declared it `RuntimeValue`. */
int64_t rt_bytes_from_raw(int64_t ptr, int64_t len) {
    /* Create a byte array ([u8]) from a raw memory pointer.
     * Used by LLVM memory buffer emission to avoid temp file I/O. */
    if (ptr == 0 || len <= 0) return (int64_t)(uintptr_t)rt_byte_array_new_len(0);
    SplArray* result = rt_byte_array_new_len((uint64_t)len);
    RtCoreArray* array = rt_core_array_ptr(result);
    if (!array || !array->data) return (int64_t)(uintptr_t)result;
    memcpy(array->data, (const void*)(uintptr_t)ptr, (size_t)len);
    return (int64_t)(uintptr_t)result;
}

/* Construct the canonical packed `[u32]` runtime array from a native pixel
 * buffer.  This is the C-bootstrap owner used before the pure-Simple
 * `simple-core` archive is available; keep the returned array in this
 * runtime's registry so normal array length/index lowering can consume it. */
int64_t rt_u32s_from_raw(int64_t ptr, int64_t count) {
    if (ptr == 0 || count <= 0) {
        return (int64_t)(uintptr_t)rt_array_new(0);
    }
    /* The bootstrap compiler's generic `[u32]` IndexGet decodes tagged array
     * elements. Use the ordinary array representation here; the typed push
     * helper applies the tag and typed accessors decode it symmetrically. */
    SplArray* result = rt_array_new(count);
    if (!result) return 0;
    const uint32_t* source = (const uint32_t*)(uintptr_t)ptr;
    for (int64_t i = 0; i < count; i++) {
        if (!rt_typed_words_u32_push(result, (int64_t)source[i])) {
            rt_array_free(result);
            return (int64_t)(uintptr_t)rt_array_new(0);
        }
    }
    return (int64_t)(uintptr_t)result;
}

/* ================================================================
 * Directory Operations (bridge to spl_ or direct libc)
 * ================================================================ */

/* rt_dir_create is already in runtime.h (takes path + recursive) but
 * LLVM IR declares it as rt_dir_create(ptr) -> i1 (single arg).
 * Provide the single-arg version. */
/* C-internal caller: `path` is a real NUL-terminated C string, so the (ptr,
 * len) pair is spelled out explicitly. rt_dir_delete itself has no
 * RuntimeFuncSpec, so it keeps the C-string signature. */
int rt_dir_delete(const char* path) {
    if (!path) return 0;
    return rt_dir_remove_all((const uint8_t*)path, (uint64_t)strlen(path)) ? 1 : 0;
}

int rt_dir_exists(const uint8_t* path_ptr, uint64_t path_len) {
    char path[RT_TEXT_PATH_MAX];
    if (!rt_text_arg_to_path(path_ptr, path_len, path, sizeof(path))) return 0;
    return rt_is_dir(path) ? 1 : 0;
}

/* ================================================================
 * Process / Environment
 * ================================================================ */

void* rt_process_spawn(const char* cmd, const char** args, int64_t arg_count) {
    /* Delegate to rt_process_spawn_async which returns pid as i64 */
    int64_t pid = rt_process_spawn_async(cmd, args, arg_count);
    return (void*)(intptr_t)pid;
}

const char* rt_getenv(const char* key) {
    return spl_env_get(key);
}

int rt_setenv(const char* key, const char* value) {
    if (!key) return 0;
#if defined(_WIN32)
    return _putenv_s(key, value ? value : "") == 0 ? 1 : 0;
#else
    int result = value ? setenv(key, value, 1) : unsetenv(key);
    return result == 0 ? 1 : 0;
#endif
}

void rt_exit(int64_t code) {
    exit((int)code);
}

void rt_cli_exit(int64_t code) {
    rt_exit(code);
}

/* ================================================================
 * Time Operations
 * ================================================================ */

int64_t rt_time_now_unix(void) {
    return (int64_t)time(NULL);
}

int64_t rt_time_now_unix_micros(void) {
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    return (int64_t)ts.tv_sec * 1000000LL + (int64_t)ts.tv_nsec / 1000LL;
}

int64_t rt_time_ms(void) {
    return rt_time_now_unix_micros() / 1000LL;
}

int64_t rt_entropy_hardware_ready(void) {
    return 0;
}

int64_t rt_time_now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000000000LL + (int64_t)ts.tv_nsec;
}

int64_t rt_time_now_nanos(void) {
    return rt_time_now_ns();
}

int64_t rt_time_now_micros(void) {
    return rt_time_now_ns() / 1000LL;
}

void rt_sleep_nanos(int64_t ns) {
    if (ns <= 0) return;
#if defined(_WIN32)
    /* Sleep has millisecond resolution. Round up so a positive deadline is
     * never converted into a zero-duration yield. */
    uint64_t remaining_ms = ((uint64_t)ns + 999999u) / 1000000u;
    while (remaining_ms > 0) {
        DWORD chunk = remaining_ms > (uint64_t)0xfffffffeu
            ? (DWORD)0xfffffffeu : (DWORD)remaining_ms;
        Sleep(chunk);
        remaining_ms -= chunk;
    }
#else
    struct timespec request;
    request.tv_sec = (time_t)(ns / 1000000000LL);
    request.tv_nsec = (long)(ns % 1000000000LL);
    while (nanosleep(&request, &request) != 0 && errno == EINTR) {
        /* Resume the exact unslept interval reported by nanosleep. */
    }
#endif
}

/* Lane-divergence fix (2026-08-01, proved by running two real linked ELFs):
 * this used to return `rt_time_now_micros() / 1000`, i.e. CLOCK_MONOTONIC
 * ms since BOOT (measured 22255054 on a box with 22255060 ms uptime), while
 * the other two lanes that implement the same public name return ms since a
 * PROCESS-START baseline and read 0 at startup:
 *   - src/runtime/runtime_time.c   (Rust-seed cdylib lane)
 *   - rt_time_now_monotonic_ms in
 *     src/compiler_rust/compiler/src/interpreter_extern/file_io.rs
 * Same symbol, two epochs ~22 million apart, no build error -- the exact
 * defect class scripts/check/check-runtime-symbol-lane-divergence.shs exists
 * to catch. Every in-tree caller uses the value as a DELTA (now - start), so
 * the divergence was latent rather than actively wrong, but any caller that
 * ever treats the reading as "elapsed since process start" (which the name
 * and the sibling lanes both promise) is silently wrong on this lane only.
 * Aligned to the process-start baseline so all three lanes agree.
 * NOTE: rt_time_now_ns / rt_time_now_nanos / rt_time_now_micros are left
 * absolute here on purpose -- they are separately tracked in
 * scripts/check/runtime_symbol_lane_divergence_baseline.txt and are owned by
 * another lane; do not "fix" them as a side effect of this one. */
int64_t rt_time_now_monotonic_ms(void) {
    static int64_t rt_monotonic_ms_baseline_ns = 0;
    static int rt_monotonic_ms_baseline_set = 0;
    int64_t now_ns = rt_time_now_ns();
    if (!rt_monotonic_ms_baseline_set) {
        rt_monotonic_ms_baseline_ns = now_ns;
        rt_monotonic_ms_baseline_set = 1;
    }
    int64_t diff_ns = now_ns - rt_monotonic_ms_baseline_ns;
    if (diff_ns < 0) diff_ns = 0;
    return diff_ns / 1000000LL;
}

void rt_sleep_ms(int64_t ms) {
    rt_sleep_ms_native(ms);
}

/* ================================================================
 * Math Operations
 * ================================================================ */

double rt_sin(double x) { return sin(x); }
double rt_cos(double x) { return cos(x); }
double rt_sqrt(double x) { return sqrt(x); }
double rt_pow(double a, double b) { return pow(a, b); }

/* ================================================================
 * Pointer Read/Write Operations (for relocation patching, FFI interop)
 * ================================================================ */

int64_t rt_ptr_read_i64(int64_t addr, int64_t offset) {
    if (addr <= 0 || offset < 0) abort();
    int64_t value;
    memcpy(&value, (char*)(uintptr_t)addr + offset, sizeof(value));
    return value;
}

int64_t rt_ptr_read_u8(int64_t addr, int64_t offset) {
    if (addr <= 0 || offset < 0) abort();
    uint8_t* ptr = (uint8_t*)((char*)(uintptr_t)addr + offset);
    return (int64_t)*ptr;
}

void rt_ptr_write_u8(int64_t addr, int64_t offset, int64_t value) {
    if (addr <= 0 || offset < 0) abort();
    uint8_t* ptr = (uint8_t*)((char*)(uintptr_t)addr + offset);
    *ptr = (uint8_t)value;
}

void rt_ptr_write_i32(int64_t addr, int64_t offset, int32_t value) {
    if (addr <= 0 || offset < 0) abort();
    int32_t* ptr = (int32_t*)((char*)(uintptr_t)addr + offset);
    *ptr = value;
}

void rt_ptr_write_i16(int64_t addr, int64_t offset, int32_t value) {
    if (addr <= 0 || offset < 0) abort();
    int16_t narrowed = (int16_t)value;
    memcpy((char*)(uintptr_t)addr + offset, &narrowed, sizeof(narrowed));
}

void rt_ptr_write_i64(int64_t addr, int64_t offset, int64_t value) {
    if (addr <= 0 || offset < 0) abort();
    int64_t* ptr = (int64_t*)((char*)(uintptr_t)addr + offset);
    *ptr = value;
}

/* Bulk write -- see runtime_memory.c for why this exists (one SFFI call per
 * section instead of one per byte). */
int64_t rt_ptr_write_bytes_raw(int64_t addr, int64_t offset, const void* src, int64_t len) {
    if (addr == 0 || src == NULL || offset < 0 || len <= 0) return 0;
    memcpy((char*)(uintptr_t)addr + offset, src, (size_t)len);
    return len;
}

/* Call a raw code address as a zero-argument int64_t function. */
int64_t rt_call_ptr_0(int64_t addr) {
    typedef int64_t (*rt_call_ptr_0_fn)(void);
    if (addr <= 0) abort();
    rt_call_ptr_0_fn f = (rt_call_ptr_0_fn)(uintptr_t)addr;
    return f();
}

int64_t rt_call_ptr_1(int64_t addr, int64_t a1) {
    typedef int64_t (*rt_call_ptr_1_fn)(int64_t);
    if (addr <= 0) abort();
    return ((rt_call_ptr_1_fn)(uintptr_t)addr)(a1);
}

int64_t rt_call_ptr_2(int64_t addr, int64_t a1, int64_t a2) {
    typedef int64_t (*rt_call_ptr_2_fn)(int64_t, int64_t);
    if (addr <= 0) abort();
    return ((rt_call_ptr_2_fn)(uintptr_t)addr)(a1, a2);
}

int64_t rt_call_ptr_3(int64_t addr, int64_t a1, int64_t a2, int64_t a3) {
    typedef int64_t (*rt_call_ptr_3_fn)(int64_t, int64_t, int64_t);
    if (addr <= 0) abort();
    return ((rt_call_ptr_3_fn)(uintptr_t)addr)(a1, a2, a3);
}

/* Exact SimpleProviderQueryV1 discovery call.  Keep this separate from the
 * generic i64 dynamic-call family: the provider ABI returns int32_t. */
int32_t rt_provider_query_v1_call(int64_t fn_ptr, int64_t request_ptr, int64_t result_ptr) {
    typedef int32_t (*simple_provider_query_v1_fn)(uint64_t, uint64_t);
    if (fn_ptr <= 0 || request_ptr <= 0 || result_ptr <= 0) return -1;
    simple_provider_query_v1_fn query = (simple_provider_query_v1_fn)(uintptr_t)fn_ptr;
    return query((uint64_t)request_ptr, (uint64_t)result_ptr);
}

/* Exact SimpleCliCommandV1 invocation call. */
int32_t rt_cli_command_v1_call(int64_t fn_ptr, int64_t interface_handle,
        int64_t provider_context, int64_t request_ptr, int64_t request_len,
        int64_t result_ptr, int64_t result_capacity) {
    typedef int32_t (*simple_cli_command_v1_fn)(uint64_t, uint64_t,
        uint64_t, uint32_t, uint64_t, uint32_t);
    if (fn_ptr <= 0 || interface_handle <= 0 || request_ptr <= 0 ||
            result_ptr <= 0 || request_len <= 0 || result_capacity <= 0 ||
            (uint64_t)request_len > UINT32_MAX ||
            (uint64_t)result_capacity > UINT32_MAX) return -1;
    simple_cli_command_v1_fn call = (simple_cli_command_v1_fn)(uintptr_t)fn_ptr;
    return call((uint64_t)interface_handle, (uint64_t)provider_context,
        (uint64_t)request_ptr, (uint32_t)request_len,
        (uint64_t)result_ptr, (uint32_t)result_capacity);
}

int64_t rt_host_dynlib_open(const uint8_t *path_ptr, int64_t path_len, int64_t mode) {
    if (!path_ptr || path_len <= 0 || path_len > 1048576) return 0;
    char *path = (char*)malloc((size_t)path_len + 1);
    if (!path) return 0;
    memcpy(path, path_ptr, (size_t)path_len);
    path[path_len] = '\0';
    int flags = ((mode & 2) ? RTLD_NOW : RTLD_LAZY) | RTLD_LOCAL;
    void *handle = dlopen(path, flags);
    free(path);
    return (int64_t)(intptr_t)handle;
}

int64_t rt_host_dynlib_symbol(int64_t handle, const uint8_t *name_ptr, int64_t name_len) {
    if (handle <= 0 || !name_ptr || name_len <= 0 || name_len > 1048576) return 0;
    char *name = (char*)malloc((size_t)name_len + 1);
    if (!name) return 0;
    memcpy(name, name_ptr, (size_t)name_len);
    name[name_len] = '\0';
    void *symbol = dlsym((void*)(intptr_t)handle, name);
    free(name);
    return (int64_t)(intptr_t)symbol;
}

int64_t rt_host_dynlib_close(int64_t handle) {
    if (handle <= 0) return -1;
    return (int64_t)dlclose((void*)(intptr_t)handle);
}

/* ================================================================
 * Error Handling
 * ================================================================ */

/* Contract-check runtime lives in its dedicated core-C archive member
 * runtime_contracts.c (a required runtime_inputs member): simple_contract_check,
 * simple_contract_check_msg, and their kind-name helper. Previously duplicated
 * here, which made the Stage4 archive reject with "defines simple_contract_check
 * 2 times"; the now-orphaned rt_contract_fail/rt_contract_kind_name/
 * rt_contract_arg_len statics were removed with them. */

/* The compiler emits the two-argument (ptr, len) form for every `text` extern
 * argument (runtime_sffi.rs:1789 declares rt_panic as &[I64, I64];
 * src/compiler/50.mir/text_extern_abi.spl decomposes the `text`). A Simple
 * `text` is NOT NUL-terminated, so the message must be copied into a bounded
 * buffer before it can be handed to spl_panic as a C string -- the same defect
 * fixed for rt_file_is_char_device in 81fca37cdd4. This one is on the FAILURE
 * path: reading past the end here corrupts the very diagnostic you would use
 * to find every other defect, so the copy is onto the stack and never
 * allocates. */
void rt_panic(const uint8_t* msg_ptr, uint64_t msg_len) {
    char buf[1024];
    if (!msg_ptr) { spl_panic("panic"); return; }
    size_t n = (size_t)msg_len;
    if (n >= sizeof(buf)) n = sizeof(buf) - 1;
    memcpy(buf, msg_ptr, n);
    buf[n] = '\0';
    spl_panic(buf);
}

void panic(int64_t msg) {
    RtCoreString* text = rt_core_as_string(msg);
    spl_panic(text ? text->data : "panic");
}

#if defined(__GNUC__) || defined(__clang__)
__attribute__((weak))
#endif
int64_t spl_str_ptr(const char* value) {
    int64_t raw = (int64_t)(uintptr_t)value;
    RtCoreString* text = rt_core_as_string(raw);
    return (int64_t)(uintptr_t)(text ? text->data : value);
}

/* ================================================================
 * Reserved-Field Cache Helpers for RtCoreString
 *
 * Bit layout (see runtime_simd_dispatch.h for constants):
 *   Bit 31     = is-ASCII validity flag
 *   Bit 30     = cp-count validity flag
 *   Bit 29     = is-ASCII value (meaningful only when bit 31 = 1)
 *   Bits [28:0] = codepoint count (meaningful only when bit 30 = 1)
 * ================================================================ */

void rt_str_cache_cp_count(RtCoreString* s, uint64_t count) {
    if (!s) return;
    if (count > SIMD_CACHE_CPCOUNT_MASK) return;
    uint32_t r = s->reserved;
    r |= SIMD_CACHE_FLAG_CPCOUNT_VALID;
    r = (r & ~SIMD_CACHE_CPCOUNT_MASK) | ((uint32_t)count & SIMD_CACHE_CPCOUNT_MASK);
    s->reserved = r;
}

int64_t rt_str_cached_cp_count(RtCoreString* s) {
    if (!s) return -1;
    if (!(s->reserved & SIMD_CACHE_FLAG_CPCOUNT_VALID)) return -1;
    return (int64_t)(s->reserved & SIMD_CACHE_CPCOUNT_MASK);
}

void rt_str_set_ascii_flag(RtCoreString* s, int is_ascii) {
    if (!s) return;
    if (is_ascii)
        s->reserved |= SIMD_CACHE_FLAG_IS_ASCII;
    /* Non-ASCII: don't cache (positive-only flag per spec) */
}

int rt_str_is_ascii_cached(RtCoreString* s) {
    if (!s) return -1;
    if (s->reserved & SIMD_CACHE_FLAG_IS_ASCII) return 1;
    return -1; /* unknown (could be ASCII or not) */
}

/* ================================================================
 * Event Loop (epoll/kqueue/IOCP/event_ports)
 * ================================================================ */

#if defined(__linux__)
#include <sys/epoll.h>

int64_t rt_event_loop_create(void) {
    return (int64_t)epoll_create1(0);
}

int64_t rt_event_loop_register(int64_t epfd, int64_t fd, int64_t mode, int64_t token, int64_t edge) {
    (void)token;
    struct epoll_event ev;
    int edge_flag = edge ? EPOLLET : 0;
    ev.events = EPOLLIN | edge_flag;
    if (mode == 1) ev.events = EPOLLOUT | edge_flag;
    else if (mode == 2) ev.events = EPOLLIN | EPOLLOUT | edge_flag;
    ev.data.fd = (int)fd;
    int rc = epoll_ctl((int)epfd, EPOLL_CTL_ADD, (int)fd, &ev);
    if (rc != 0 && errno == EEXIST) {
        rc = epoll_ctl((int)epfd, EPOLL_CTL_MOD, (int)fd, &ev);
    }
    return rc == 0 ? 1 : 0;
}

int64_t rt_event_loop_deregister(int64_t epfd, int64_t fd) {
    int rc = epoll_ctl((int)epfd, EPOLL_CTL_DEL, (int)fd, NULL);
    if (rc != 0 && errno == ENOENT) return 1;
    return rc == 0 ? 1 : 0;
}

static int64_t poll_results[256];

int64_t rt_event_loop_poll(int64_t epfd, int64_t max_events, int64_t timeout_ms) {
    struct epoll_event events[256];
    if (max_events > 256) max_events = 256;
    int n = epoll_wait((int)epfd, events, (int)max_events, (int)timeout_ms);
    if (n < 0) return 0;
    for (int i = 0; i < n; i++) {
        poll_results[i] = (int64_t)events[i].data.fd;
    }
    return (int64_t)n;
}

int64_t rt_event_loop_close(int64_t epfd) {
    return (int64_t)close((int)epfd);
}

#elif defined(__APPLE__) || defined(__FreeBSD__)
#include <sys/event.h>

int64_t rt_event_loop_create(void) {
    return (int64_t)kqueue();
}

int64_t rt_event_loop_register(int64_t kqfd, int64_t fd, int64_t mode, int64_t token, int64_t edge) {
    (void)token;
    struct kevent ev[2];
    uint16_t flags = EV_ADD;
    if (edge) flags = flags | EV_CLEAR;
    int count = 1;
    if (mode == 1) {
        EV_SET(&ev[0], (uintptr_t)fd, EVFILT_WRITE, flags, 0, 0, NULL);
    } else if (mode == 2) {
        EV_SET(&ev[0], (uintptr_t)fd, EVFILT_READ, flags, 0, 0, NULL);
        EV_SET(&ev[1], (uintptr_t)fd, EVFILT_WRITE, flags, 0, 0, NULL);
        count = 2;
    } else {
        EV_SET(&ev[0], (uintptr_t)fd, EVFILT_READ, flags, 0, 0, NULL);
    }
    int rc = kevent((int)kqfd, ev, count, NULL, 0, NULL);
    return rc == 0 ? 1 : 0;
}

int64_t rt_event_loop_deregister(int64_t kqfd, int64_t fd) {
    struct kevent ev[2];
    EV_SET(&ev[0], (uintptr_t)fd, EVFILT_READ, EV_DELETE, 0, 0, NULL);
    EV_SET(&ev[1], (uintptr_t)fd, EVFILT_WRITE, EV_DELETE, 0, 0, NULL);
    int rc = kevent((int)kqfd, ev, 2, NULL, 0, NULL);
    if (rc != 0 && errno == ENOENT) return 1;
    return rc == 0 ? 1 : 0;
}

static int64_t poll_results[256];

int64_t rt_event_loop_poll(int64_t kqfd, int64_t max_events, int64_t timeout_ms) {
    struct kevent events[256];
    if (max_events > 256) max_events = 256;
    struct timespec ts;
    ts.tv_sec = timeout_ms / 1000;
    ts.tv_nsec = (timeout_ms % 1000) * 1000000;
    int n = kevent((int)kqfd, NULL, 0, events, (int)max_events, &ts);
    if (n < 0) return 0;
    for (int i = 0; i < n; i++) {
        poll_results[i] = (int64_t)events[i].ident;
    }
    return (int64_t)n;
}

int64_t rt_event_loop_close(int64_t kqfd) {
    return (int64_t)close((int)kqfd);
}

#else

int64_t rt_event_loop_create(void) { return -1; }
int64_t rt_event_loop_register(int64_t h, int64_t fd, int64_t mode, int64_t token, int64_t edge) { (void)h; (void)fd; (void)mode; (void)token; (void)edge; return -1; }
int64_t rt_event_loop_deregister(int64_t h, int64_t fd) { (void)h; (void)fd; return -1; }
static int64_t poll_results[256];
int64_t rt_event_loop_poll(int64_t h, int64_t max, int64_t ms) { (void)h; (void)max; (void)ms; return 0; }
int64_t rt_event_loop_close(int64_t h) { (void)h; return -1; }

#endif

int64_t rt_event_loop_poll_get_fd(int64_t index) {
    if (index < 0 || index >= 256) return -1;
    return poll_results[index];
}

int64_t rt_kqueue_create(void) { return rt_event_loop_create(); }
int64_t rt_kqueue_register(int64_t h, int64_t fd, int64_t m) { return rt_event_loop_register(h, fd, m, fd, 1); }
int64_t rt_kqueue_deregister(int64_t h, int64_t fd) { return rt_event_loop_deregister(h, fd); }
int64_t rt_kqueue_poll(int64_t h, int64_t max, int64_t ms) { return rt_event_loop_poll(h, max, ms); }
int64_t rt_kqueue_close(int64_t h) { return rt_event_loop_close(h); }

int64_t rt_iocp_create(void) { return -1; }
int64_t rt_iocp_register(int64_t h, int64_t fd, int64_t m) { (void)h; (void)fd; (void)m; return -1; }
int64_t rt_iocp_poll(int64_t h, int64_t max, int64_t ms) { (void)h; (void)max; (void)ms; return 0; }
int64_t rt_iocp_close(int64_t h) { (void)h; return -1; }

int64_t rt_event_ports_create(void) { return -1; }
int64_t rt_event_ports_register(int64_t h, int64_t fd, int64_t m) { (void)h; (void)fd; (void)m; return -1; }
int64_t rt_event_ports_poll(int64_t h, int64_t max, int64_t ms) { (void)h; (void)max; (void)ms; return 0; }
int64_t rt_event_ports_close(int64_t h) { (void)h; return -1; }


/* ================================================================
 * TCP Socket Functions — all params int64_t (tagged values from LLVM codegen)
 * text = int64_t tagged heap pointer; extract via rt_core_as_string()
 * ================================================================ */

#if !defined(_WIN32)

static const char* rt_extract_cstr(int64_t text_val) {
    RtCoreString* s = rt_core_as_string(text_val);
    return s ? s->data : NULL;
}

static int rt_parse_addr_port(const char* addr_str, struct sockaddr_in* sa) {
    if (!addr_str || !sa) return -1;
    memset(sa, 0, sizeof(*sa));
    sa->sin_family = AF_INET;
    char buf[256];
    size_t alen = strlen(addr_str);
    if (alen >= sizeof(buf)) return -1;
    memcpy(buf, addr_str, alen + 1);
    char* colon = strrchr(buf, ':');
    if (!colon) return -1;
    *colon = '\0';
    int port = atoi(colon + 1);
    sa->sin_port = htons((uint16_t)port);
    if (buf[0] == '\0' || strcmp(buf, "0.0.0.0") == 0)
        sa->sin_addr.s_addr = INADDR_ANY;
    else if (inet_pton(AF_INET, buf, &sa->sin_addr) != 1)
        return -1;
    return 0;
}

static int64_t rt_make_addr_string(struct sockaddr_in* sa) {
    char ip[INET_ADDRSTRLEN];
    inet_ntop(AF_INET, &sa->sin_addr, ip, sizeof(ip));
    char buf[80];
    int n = snprintf(buf, sizeof(buf), "%s:%d", ip, ntohs(sa->sin_port));
    return rt_string_new((const uint8_t*)buf, (uint64_t)n);
}

int64_t rt_io_tcp_socket_create(int64_t family) {
    int af = (family == 6) ? AF_INET6 : AF_INET;
    return (int64_t)socket(af, SOCK_STREAM, 0);
}

int64_t rt_io_tcp_bind(int64_t addr_val) {
    const char* a = rt_extract_cstr(addr_val);
    if (!a) return -1;
    struct sockaddr_in sa;
    if (rt_parse_addr_port(a, &sa) < 0) return -1;
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return -1;
    int opt = 1;
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));
    if (bind(fd, (struct sockaddr*)&sa, sizeof(sa)) < 0) { close(fd); return -1; }
    return (int64_t)fd;
}

int64_t rt_io_tcp_bind_fd(int64_t fd, int64_t addr_val) {
    const char* a = rt_extract_cstr(addr_val);
    if (!a) return 0;
    struct sockaddr_in sa;
    if (rt_parse_addr_port(a, &sa) < 0) return 0;
    return bind((int)fd, (struct sockaddr*)&sa, sizeof(sa)) == 0 ? 1 : 0;
}

int64_t rt_io_tcp_listen(int64_t fd, int64_t backlog) {
    return listen((int)fd, (int)backlog) == 0 ? 1 : 0;
}

int64_t rt_io_tcp_accept(int64_t fd) {
    struct sockaddr_in cl;
    socklen_t len = sizeof(cl);
    return (int64_t)accept((int)fd, (struct sockaddr*)&cl, &len);
}

int64_t rt_io_tcp_accept_timeout(int64_t fd, int64_t ms) {
    struct pollfd pfd;
    memset(&pfd, 0, sizeof(pfd));
    pfd.fd = (int)fd; pfd.events = POLLIN;
    if (poll(&pfd, 1, (int)ms) <= 0) return -1;
    return rt_io_tcp_accept(fd);
}

int64_t rt_io_tcp_connect(int64_t addr_val) {
    const char* a = rt_extract_cstr(addr_val);
    if (!a) return -1;
    struct sockaddr_in sa;
    if (rt_parse_addr_port(a, &sa) < 0) return -1;
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return -1;
    if (connect(fd, (struct sockaddr*)&sa, sizeof(sa)) < 0) { close(fd); return -1; }
    return (int64_t)fd;
}

int64_t rt_io_tcp_connect_timeout(int64_t addr_val, int64_t ms) {
    (void)ms;
    return rt_io_tcp_connect(addr_val);
}

int64_t rt_io_tcp_read(int64_t fd, int64_t size) {
    SplArray* arr = rt_byte_array_new((uint64_t)size);
    RtCoreArray* ca = rt_core_array_ptr(arr);
    if (!ca || !ca->data) return (int64_t)(uintptr_t)arr;
    ssize_t n = read((int)fd, ca->data, (size_t)size);
    ca->len = n > 0 ? n : 0;
    return (int64_t)(uintptr_t)arr;
}

int64_t rt_io_tcp_read_line(int64_t fd) {
    char buf[4096];
    int pos = 0;
    while (pos < (int)sizeof(buf) - 1) {
        ssize_t n = read((int)fd, &buf[pos], 1);
        if (n <= 0) break;
        if (buf[pos] == '\n') { pos++; break; }
        pos++;
    }
    if (pos == 0) return rt_core_nil();
    return rt_string_new((const uint8_t*)buf, (uint64_t)pos);
}

int64_t rt_io_tcp_write(int64_t fd, int64_t data_val) {
    RtCoreArray* ca = rt_core_array_ptr((SplArray*)(uintptr_t)data_val);
    if (!ca || !ca->data || ca->len <= 0) return 0;
    return (int64_t)write((int)fd, ca->data, (size_t)ca->len);
}

int64_t rt_io_tcp_write_text(int64_t fd, int64_t text_val) {
    RtCoreString* s = rt_core_as_string(text_val);
    if (!s || s->len == 0) return 0;
    return (int64_t)write((int)fd, s->data, (size_t)s->len);
}

int64_t rt_io_tcp_write_bytes(int64_t fd, int64_t data_val) {
    return rt_io_tcp_write(fd, data_val);
}

int64_t rt_io_tcp_flush(int64_t fd) {
    int flag = 1;
    setsockopt((int)fd, IPPROTO_TCP, TCP_NODELAY, &flag, sizeof(flag));
    flag = 0;
    setsockopt((int)fd, IPPROTO_TCP, TCP_NODELAY, &flag, sizeof(flag));
    return 1;
}

int64_t rt_io_tcp_close(int64_t fd) {
    return close((int)fd) == 0 ? 1 : 0;
}

int64_t rt_io_tcp_local_addr(int64_t fd) {
    struct sockaddr_in sa;
    socklen_t len = sizeof(sa);
    if (getsockname((int)fd, (struct sockaddr*)&sa, &len) < 0) return rt_core_nil();
    return rt_make_addr_string(&sa);
}

int64_t rt_io_tcp_peer_addr(int64_t fd) {
    struct sockaddr_in sa;
    socklen_t len = sizeof(sa);
    if (getpeername((int)fd, (struct sockaddr*)&sa, &len) < 0) return rt_core_nil();
    return rt_make_addr_string(&sa);
}

int64_t rt_io_tcp_set_nonblocking(int64_t fd, int64_t enabled) {
    int flags = fcntl((int)fd, F_GETFL, 0);
    if (flags < 0) return 0;
    if (enabled) flags |= O_NONBLOCK; else flags &= ~O_NONBLOCK;
    return fcntl((int)fd, F_SETFL, flags) == 0 ? 1 : 0;
}

int64_t rt_io_tcp_set_nodelay(int64_t fd, int64_t enabled) {
    int flag = enabled ? 1 : 0;
    return setsockopt((int)fd, IPPROTO_TCP, TCP_NODELAY, &flag, sizeof(flag)) == 0 ? 1 : 0;
}

int64_t rt_io_tcp_set_reuseport(int64_t fd, int64_t enabled) {
#ifdef SO_REUSEPORT
    int flag = enabled ? 1 : 0;
    return setsockopt((int)fd, SOL_SOCKET, SO_REUSEPORT, &flag, sizeof(flag)) == 0 ? 1 : 0;
#else
    (void)fd; (void)enabled; return 0;
#endif
}

int64_t rt_io_tcp_set_reuseaddr(int64_t fd, int64_t enabled) {
    int flag = enabled ? 1 : 0;
    return setsockopt((int)fd, SOL_SOCKET, SO_REUSEADDR, &flag, sizeof(flag)) == 0 ? 1 : 0;
}

int64_t rt_io_tcp_set_read_timeout(int64_t fd, int64_t ms) {
    struct timeval tv;
    tv.tv_sec = ms / 1000; tv.tv_usec = (ms % 1000) * 1000;
    return setsockopt((int)fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv)) == 0 ? 1 : 0;
}

int64_t rt_io_tcp_set_write_timeout(int64_t fd, int64_t ms) {
    struct timeval tv;
    tv.tv_sec = ms / 1000; tv.tv_usec = (ms % 1000) * 1000;
    return setsockopt((int)fd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof(tv)) == 0 ? 1 : 0;
}

int64_t rt_io_tcp_shutdown(int64_t fd, int64_t how) {
    return shutdown((int)fd, (int)how) == 0 ? 1 : 0;
}

/* ================================================================
 * UDP Socket Functions
 * ================================================================ */

int64_t rt_io_udp_bind(int64_t addr_val) {
    const char* a = rt_extract_cstr(addr_val);
    if (!a) return -1;
    struct sockaddr_in sa;
    if (rt_parse_addr_port(a, &sa) < 0) return -1;
    int fd = socket(AF_INET, SOCK_DGRAM, 0);
    if (fd < 0) return -1;
    int opt = 1;
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));
    if (bind(fd, (struct sockaddr*)&sa, sizeof(sa)) < 0) { close(fd); return -1; }
    return (int64_t)fd;
}

int64_t rt_io_udp_send_to(int64_t fd, int64_t data_val, int64_t addr_val) {
    const char* a = rt_extract_cstr(addr_val);
    if (!a) return -1;
    RtCoreArray* ca = rt_core_array_ptr((SplArray*)(uintptr_t)data_val);
    if (!ca || !ca->data || ca->len <= 0) return 0;
    struct sockaddr_in sa;
    if (rt_parse_addr_port(a, &sa) < 0) return -1;
    return (int64_t)sendto((int)fd, ca->data, (size_t)ca->len, 0, (struct sockaddr*)&sa, sizeof(sa));
}

int64_t rt_io_udp_send(int64_t fd, int64_t data_val) {
    RtCoreArray* ca = rt_core_array_ptr((SplArray*)(uintptr_t)data_val);
    if (!ca || !ca->data || ca->len <= 0) return 0;
    return (int64_t)send((int)fd, ca->data, (size_t)ca->len, 0);
}

int64_t rt_io_udp_recv(int64_t fd, int64_t size) {
    SplArray* arr = rt_byte_array_new((uint64_t)size);
    RtCoreArray* ca = rt_core_array_ptr(arr);
    if (!ca || !ca->data) return (int64_t)(uintptr_t)arr;
    ssize_t n = recv((int)fd, ca->data, (size_t)size, 0);
    ca->len = n > 0 ? n : 0;
    return (int64_t)(uintptr_t)arr;
}

int64_t rt_io_udp_connect(int64_t fd, int64_t addr_val) {
    const char* a = rt_extract_cstr(addr_val);
    if (!a) return 0;
    struct sockaddr_in sa;
    if (rt_parse_addr_port(a, &sa) < 0) return 0;
    return connect((int)fd, (struct sockaddr*)&sa, sizeof(sa)) == 0 ? 1 : 0;
}

int64_t rt_io_udp_local_addr(int64_t fd) { return rt_io_tcp_local_addr(fd); }
int64_t rt_io_udp_set_broadcast(int64_t fd, int64_t e) {
    int flag = e ? 1 : 0;
    return setsockopt((int)fd, SOL_SOCKET, SO_BROADCAST, &flag, sizeof(flag)) == 0 ? 1 : 0;
}
int64_t rt_io_udp_set_read_timeout(int64_t fd, int64_t ms) { return rt_io_tcp_set_read_timeout(fd, ms); }
int64_t rt_io_udp_close(int64_t fd) { return close((int)fd) == 0 ? 1 : 0; }
int64_t rt_io_udp_set_nonblocking(int64_t fd, int64_t e) { return rt_io_tcp_set_nonblocking(fd, e); }

int64_t rt_io_udp_recv_from(int64_t fd, int64_t size) {
    SplArray* arr = rt_byte_array_new((uint64_t)size);
    RtCoreArray* ca = rt_core_array_ptr(arr);
    if (!ca || !ca->data) return (int64_t)(uintptr_t)arr;
    struct sockaddr_in from;
    socklen_t fromlen = sizeof(from);
    ssize_t n = recvfrom((int)fd, ca->data, (size_t)size, 0, (struct sockaddr*)&from, &fromlen);
    ca->len = n > 0 ? n : 0;
    return (int64_t)(uintptr_t)arr;
}

#else /* _WIN32 stubs */
int64_t rt_io_tcp_socket_create(int64_t f) { (void)f; return -1; }
int64_t rt_io_tcp_bind(int64_t a) { (void)a; return -1; }
int64_t rt_io_tcp_bind_fd(int64_t f, int64_t a) { (void)f; (void)a; return 0; }
int64_t rt_io_tcp_listen(int64_t f, int64_t b) { (void)f; (void)b; return 0; }
int64_t rt_io_tcp_accept(int64_t f) { (void)f; return -1; }
int64_t rt_io_tcp_accept_timeout(int64_t f, int64_t m) { (void)f; (void)m; return -1; }
int64_t rt_io_tcp_connect(int64_t a) { (void)a; return -1; }
int64_t rt_io_tcp_connect_timeout(int64_t a, int64_t m) { (void)a; (void)m; return -1; }
int64_t rt_io_tcp_read(int64_t f, int64_t s) { (void)f; (void)s; return 0; }
int64_t rt_io_tcp_read_line(int64_t f) { (void)f; return 0; }
int64_t rt_io_tcp_write(int64_t f, int64_t d) { (void)f; (void)d; return 0; }
int64_t rt_io_tcp_write_text(int64_t f, int64_t d) { (void)f; (void)d; return 0; }
int64_t rt_io_tcp_write_bytes(int64_t f, int64_t d) { (void)f; (void)d; return 0; }
int64_t rt_io_tcp_flush(int64_t f) { (void)f; return 0; }
int64_t rt_io_tcp_close(int64_t f) { (void)f; return 0; }
int64_t rt_io_tcp_local_addr(int64_t f) { (void)f; return 0; }
int64_t rt_io_tcp_peer_addr(int64_t f) { (void)f; return 0; }
int64_t rt_io_tcp_set_nonblocking(int64_t f, int64_t e) { (void)f; (void)e; return 0; }
int64_t rt_io_tcp_set_nodelay(int64_t f, int64_t e) { (void)f; (void)e; return 0; }
int64_t rt_io_tcp_set_reuseport(int64_t f, int64_t e) { (void)f; (void)e; return 0; }
int64_t rt_io_tcp_set_reuseaddr(int64_t f, int64_t e) { (void)f; (void)e; return 0; }
int64_t rt_io_tcp_set_read_timeout(int64_t f, int64_t m) { (void)f; (void)m; return 0; }
int64_t rt_io_tcp_set_write_timeout(int64_t f, int64_t m) { (void)f; (void)m; return 0; }
int64_t rt_io_tcp_shutdown(int64_t f, int64_t h) { (void)f; (void)h; return 0; }
int64_t rt_io_udp_bind(int64_t a) { (void)a; return -1; }
int64_t rt_io_udp_send_to(int64_t f, int64_t d, int64_t a) { (void)f; (void)d; (void)a; return 0; }
int64_t rt_io_udp_send(int64_t f, int64_t d) { (void)f; (void)d; return 0; }
int64_t rt_io_udp_recv(int64_t f, int64_t s) { (void)f; (void)s; return 0; }
int64_t rt_io_udp_connect(int64_t f, int64_t a) { (void)f; (void)a; return 0; }
int64_t rt_io_udp_local_addr(int64_t f) { (void)f; return 0; }
int64_t rt_io_udp_set_broadcast(int64_t f, int64_t e) { (void)f; (void)e; return 0; }
int64_t rt_io_udp_set_read_timeout(int64_t f, int64_t m) { (void)f; (void)m; return 0; }
int64_t rt_io_udp_close(int64_t f) { (void)f; return 0; }
int64_t rt_io_udp_set_nonblocking(int64_t f, int64_t e) { (void)f; (void)e; return 0; }
int64_t rt_io_udp_recv_from(int64_t f, int64_t s) { (void)f; (void)s; return 0; }
#endif /* !_WIN32 */

/* ================================================================
 * Channel Functions (simple mutex-based queue)
 * ================================================================ */

#if !defined(_WIN32)

#define RT_CHAN_MAX 64
#define RT_CHAN_QSIZE 1024

typedef struct {
    pthread_mutex_t lock;
    pthread_cond_t  not_empty;
    int64_t*        queue;
    int             capacity;
    int             head, tail, count;
    int             closed, in_use;
} RtChannel;

static RtChannel rt_channels[RT_CHAN_MAX];
static int rt_chan_init_done = 0;

int64_t rt_channel_new(void) {
    if (!rt_chan_init_done) { rt_chan_init_done = 1; memset(rt_channels, 0, sizeof(rt_channels)); }
    for (int i = 0; i < RT_CHAN_MAX; i++) {
        if (!rt_channels[i].in_use) {
            RtChannel* ch = &rt_channels[i];
            pthread_mutex_init(&ch->lock, NULL);
            pthread_cond_init(&ch->not_empty, NULL);
            ch->queue = (int64_t*)malloc(sizeof(int64_t) * RT_CHAN_QSIZE);
            if (!ch->queue) {
                pthread_cond_destroy(&ch->not_empty);
                pthread_mutex_destroy(&ch->lock);
                return -1;
            }
            ch->capacity = RT_CHAN_QSIZE;
            ch->head = ch->tail = ch->count = 0;
            ch->closed = 0; ch->in_use = 1;
            return (int64_t)i;
        }
    }
    return -1;
}

/* Returns 1 when the value was queued, 0 when the channel id was invalid,
 * unused, or already closed. runtime_sffi.rs:811 declares `-> &[I64]` and
 * src/compiler_rust/lib/std/src/async/sffi/channel.spl:7 declares
 * `-> bool` and is a LIVE consumer, so the void form handed that caller an
 * uninitialised register as "the send succeeded". */
int64_t rt_channel_send(int64_t id, int64_t value) {
    if (id < 0 || id >= RT_CHAN_MAX) return 0;
    RtChannel* ch = &rt_channels[id];
    if (!ch->in_use || ch->closed) return 0;
    pthread_mutex_lock(&ch->lock);
    if (ch->count == ch->capacity) {
        int new_capacity = ch->capacity * 2;
        int64_t* grown = (int64_t*)malloc(sizeof(int64_t) * new_capacity);
        if (!grown) {
            pthread_mutex_unlock(&ch->lock);
            fprintf(stderr, "rt_channel_send: failed to grow channel buffer\n");
            abort();
        }
        for (int i = 0; i < ch->count; i++) {
            grown[i] = ch->queue[(ch->head + i) % ch->capacity];
        }
        free(ch->queue);
        ch->queue = grown;
        ch->capacity = new_capacity;
        ch->head = 0;
        ch->tail = ch->count;
    }
    ch->queue[ch->tail] = value;
    ch->tail = (ch->tail + 1) % ch->capacity;
    ch->count++;
    pthread_cond_signal(&ch->not_empty);
    pthread_mutex_unlock(&ch->lock);
    return 1;
}

int64_t rt_channel_recv(int64_t id) {
    if (id < 0 || id >= RT_CHAN_MAX) return 0;
    RtChannel* ch = &rt_channels[id];
    if (!ch->in_use) return 0;
    pthread_mutex_lock(&ch->lock);
    while (ch->count == 0 && !ch->closed)
        pthread_cond_wait(&ch->not_empty, &ch->lock);
    int64_t val = 0;
    if (ch->count > 0) {
        val = ch->queue[ch->head];
        ch->head = (ch->head + 1) % ch->capacity;
        ch->count--;
    }
    pthread_mutex_unlock(&ch->lock);
    return val;
}

int64_t rt_channel_try_recv(int64_t id) {
    if (id < 0 || id >= RT_CHAN_MAX) return 0;
    RtChannel* ch = &rt_channels[id];
    if (!ch->in_use) return 0;
    pthread_mutex_lock(&ch->lock);
    int64_t val = 0;
    if (ch->count > 0) {
        val = ch->queue[ch->head];
        ch->head = (ch->head + 1) % ch->capacity;
        ch->count--;
    }
    pthread_mutex_unlock(&ch->lock);
    return val;
}

void rt_channel_close(int64_t id) {
    if (id < 0 || id >= RT_CHAN_MAX) return;
    RtChannel* ch = &rt_channels[id];
    if (!ch->in_use) return;
    pthread_mutex_lock(&ch->lock);
    ch->closed = 1;
    pthread_cond_broadcast(&ch->not_empty);
    pthread_mutex_unlock(&ch->lock);
}

int64_t rt_channel_is_closed(int64_t id) {
    if (id < 0 || id >= RT_CHAN_MAX) return 1;
    return rt_channels[id].closed ? 1 : 0;
}

#else
int64_t rt_channel_new(void) { return -1; }
int64_t rt_channel_send(int64_t id, int64_t v) { (void)id; (void)v; return 0; }
int64_t rt_channel_recv(int64_t id) { (void)id; return 0; }
int64_t rt_channel_try_recv(int64_t id) { (void)id; return 0; }
void rt_channel_close(int64_t id) { (void)id; }
int64_t rt_channel_is_closed(int64_t id) { (void)id; return 1; }
#endif

/* ================================================================
 * CPUID and architecture-gate helpers
 * ================================================================ */

#if defined(__x86_64__) || defined(_M_X64)
#  if defined(_MSC_VER)
#    include <intrin.h>
#  else
#    include <cpuid.h>
#  endif
#endif

typedef struct { int32_t a, b, c, d; } RtCpuidResult;

RtCpuidResult rt_cpuid(int32_t leaf, int32_t subleaf) {
    RtCpuidResult r = {0, 0, 0, 0};
#if defined(__x86_64__) || defined(_M_X64)
#  if defined(_MSC_VER)
    int regs[4];
    __cpuidex(regs, (int)leaf, (int)subleaf);
    r.a = regs[0]; r.b = regs[1]; r.c = regs[2]; r.d = regs[3];
#  else
    __cpuid_count((unsigned int)leaf, (unsigned int)subleaf,
                  *(unsigned int*)&r.a, *(unsigned int*)&r.b,
                  *(unsigned int*)&r.c, *(unsigned int*)&r.d);
#  endif
#else
    (void)leaf; (void)subleaf;
#endif
    return r;
}

int32_t rt_cpu_is_x86_64(void) {
#if defined(__x86_64__) || defined(_M_X64)
    return 1;
#else
    return 0;
#endif
}

int32_t rt_cpu_is_aarch64(void) {
#if defined(__aarch64__) || defined(_M_ARM64)
    return 1;
#else
    return 0;
#endif
}

int32_t rt_cpu_is_riscv64(void) {
#if defined(__riscv) && (__riscv_xlen == 64)
    return 1;
#else
    return 0;
#endif
}

/* ================================================================
 * Runtime Lifecycle (called by entry point)
 * ================================================================ */

void __simple_runtime_init(void) {
}

void __simple_runtime_shutdown(void) {
    fflush(stdout);
    fflush(stderr);
}

/* ================================================================
 * Codegen-emitted runtime symbols that had NO definition anywhere
 * ================================================================
 *
 * Bug: doc/08_tracking/bug/c_runtime_missing_83_codegen_runtime_symbols_2026-08-21.md
 *
 * `scripts/check/check-no-unresolved-runtime-symbols.shs` found 84 `rt_*` names
 * that codegen hands to an emitter but that nothing in the tree defines. The
 * native link tolerates undefined symbols, so each one became a NULL GOT slot
 * and SEGV'd on first call -- that is how `rt_unwrap_or_trap` killed every
 * self-hosted stage binary on a three-line hello world while `--version`
 * answered cleanly.
 *
 * Two honest outcomes are possible per symbol, and NOTHING here fabricates a
 * plausible-looking value for the third case:
 *
 *   (1) Real semantics, taken from the Rust runtime (`src/compiler_rust/
 *       runtime/src/value/objects.rs`) or `src/runtime/simple_core/*.spl`.
 *   (2) A NAMED LOUD TRAP -- `rt_trap_unimplemented("rt_x")` prints the symbol
 *       to stderr and aborts. This is a STUB, not an implementation. It is
 *       strictly better than address 0 (you learn WHICH call died) and strictly
 *       worse than the real thing (the program still dies).
 */

void rt_trap_unimplemented(const char *symbol) {
    fprintf(stderr,
            "simple runtime: unimplemented runtime entrypoint `%s` was called.\n"
            "  This is a NAMED TRAP stub, not an implementation. See\n"
            "  doc/08_tracking/bug/c_runtime_missing_83_codegen_runtime_symbols_2026-08-21.md\n",
            symbol ? symbol : "(null)");
    fflush(stderr);
    abort();
}

/* ---- Option / Result construction -------------------------------------
 * Mirrors rt_option_some/rt_option_none in the Rust runtime, which build a
 * canonical enum with the reserved Option enum_id 1 and the stable 32-bit
 * variant-name hashes. Result has no reserved enum_id; the same hashes are
 * already the identification key used by rt_unwrap_or_trap above, so Ok/Err
 * are constructed with them here. Keeping these four consistent with
 * rt_unwrap_or_trap is what makes `?`/`??`/`.unwrap()` agree. */
#define SPL_OPTION_ENUM_ID   1
#define SPL_RESULT_ENUM_ID   2
#define SPL_HASH_SOME 4053299545u
#define SPL_HASH_NONE 2371748697u
#define SPL_HASH_OK   2405352012u
#define SPL_HASH_ERR  4200179024u

/* `.unwrap()` on Option/Result: yield the payload, or ABORT. This is the exact
 * symbol whose absence SEGV'd every self-hosted stage binary on hello world
 * (stage3_native_build_and_compile_segv_on_hello_world_2026-08-18) -- the C
 * runtime, the one the bootstrap/native lane actually links, only ever
 * MENTIONED it in a comment. Semantics transcribed from the pure-Simple
 * definition in src/runtime/simple_core/core_values.spl:78, which is the
 * canonical one: ordinal discriminants for the reserved Option enum_id 1, and
 * the stable 32-bit variant-name hashes for Result, which has no reserved id. */
int64_t rt_unwrap_or_trap(int64_t value) {
    int64_t enum_id = rt_enum_id(value);
    int64_t discriminant;
    if (enum_id < 0) return value;
    discriminant = rt_enum_discriminant(value);
    if (enum_id == SPL_OPTION_ENUM_ID) {
        if (discriminant == 0 || discriminant == (int64_t)SPL_HASH_SOME) return rt_enum_payload(value);
        if (discriminant == 1 || discriminant == (int64_t)SPL_HASH_NONE) {
            fprintf(stderr, "simple runtime: .unwrap() called on None\n");
            fflush(stderr);
            abort();
        }
        return value;
    }
    if (discriminant == (int64_t)SPL_HASH_OK) return rt_enum_payload(value);
    if (discriminant == (int64_t)SPL_HASH_ERR) {
        fprintf(stderr, "simple runtime: .unwrap() called on Err\n");
        fflush(stderr);
        abort();
    }
    return value;
}

int64_t rt_option_some(int64_t payload) {
    return rt_enum_new(SPL_OPTION_ENUM_ID, (int32_t)SPL_HASH_SOME, payload);
}

int64_t rt_option_none(void) {
    return rt_enum_new(SPL_OPTION_ENUM_ID, (int32_t)SPL_HASH_NONE, rt_value_nil());
}

int64_t rt_result_ok(int64_t payload) {
    return rt_enum_new(SPL_RESULT_ENUM_ID, (int32_t)SPL_HASH_OK, payload);
}

int64_t rt_result_err(int64_t payload) {
    return rt_enum_new(SPL_RESULT_ENUM_ID, (int32_t)SPL_HASH_ERR, payload);
}

/* `?` propagation: yield the Some/Ok payload, otherwise hand the wrapper back
 * so the caller's propagation path can return it unchanged. Deliberately does
 * NOT trap -- that is rt_unwrap_or_trap's job, and conflating the two is the
 * defect recorded in native_unwrap_returns_enum_wrapper_instead_of_payload. */
int64_t rt_try_unwrap(int64_t value) {
    int64_t d;
    if (rt_enum_id(value) < 0) return value;
    d = rt_enum_discriminant(value);
    if (d == 0 || d == (int64_t)(uint32_t)SPL_HASH_SOME || d == (int64_t)(uint32_t)SPL_HASH_OK) {
        return rt_enum_payload(value);
    }
    return value;
}

/* ---- Unions -----------------------------------------------------------
 * emit_union_wrap passes (value, type_index); the index IS the discriminant,
 * so this round-trips exactly through the enum representation. */
#define SPL_UNION_ENUM_ID 3

int64_t rt_union_wrap(int64_t value, int64_t type_index) {
    return rt_enum_new(SPL_UNION_ENUM_ID, (int32_t)type_index, value);
}

int64_t rt_union_discriminant(int64_t value) {
    return rt_enum_discriminant(value);
}

int64_t rt_union_payload(int64_t value) {
    return rt_enum_payload(value);
}

/* ---- Pattern matching / enum construction: NAMED TRAPS ------------------
 * These are traps for a reason that is NOT "nobody got around to it". The
 * LLVM emitter DISCARDS the information the runtime would need:
 *   emit_pattern_test(dest, subject, _pattern)      -- pattern dropped
 *   emit_pattern_bind(dest, subject, _binding)      -- binding dropped
 *   emit_enum_unit(dest, _enum_name, _variant_name) -- both names dropped,
 *                                                      literal 0 passed instead
 *   emit_enum_with(dest, _enum_name, _variant_name, payload) -- names dropped
 * (src/compiler_rust/compiler/src/codegen/llvm/emitter.rs:1703-1745)
 * With the pattern and the variant identity gone, EVERY return value is a
 * fabrication: `rt_pattern_test` returning 0 silently takes the wrong match
 * arm, and `rt_enum_unit(0)` builds a variant of the wrong enum. Trapping
 * loudly is the only answer that does not corrupt the program. Fixing this
 * properly requires changing the emitter to pass the dropped operands -- filed
 * separately in the bug record. */
int64_t rt_pattern_test(int64_t subject) {
    (void)subject;
    rt_trap_unimplemented("rt_pattern_test");
    return 0;
}

int64_t rt_pattern_bind(int64_t subject) {
    (void)subject;
    rt_trap_unimplemented("rt_pattern_bind");
    return 0;
}

int64_t rt_enum_unit(int64_t discriminant) {
    (void)discriminant;
    rt_trap_unimplemented("rt_enum_unit");
    return 0;
}

int64_t rt_enum_with(int64_t payload) {
    (void)payload;
    rt_trap_unimplemented("rt_enum_with");
    return 0;
}

/* ---- GPU intrinsics: NAMED TRAPS ---------------------------------------
 * Every rt_gpu_* below is a STUB. On the host CPU there is no work-item, no
 * work-group, and no device-shared memory, so there is no correct value to
 * return: `rt_gpu_global_id()` answering 0 makes a kernel silently compute
 * element 0 for every thread. These abort with their own name instead of
 * jumping to address 0. Real host-side emulation (or a hard compile-time
 * rejection of GPU intrinsics outside a kernel) is the actual fix. */
#define SPL_GPU_TRAP0(name)                    \
    int64_t name(void) {                       \
        rt_trap_unimplemented(#name);          \
        return 0;                              \
    }
#define SPL_GPU_TRAP1(name)                    \
    int64_t name(int64_t a) {                  \
        (void)a;                               \
        rt_trap_unimplemented(#name);          \
        return 0;                              \
    }
#define SPL_GPU_TRAP2(name)                    \
    int64_t name(int64_t a, int64_t b) {       \
        (void)a; (void)b;                      \
        rt_trap_unimplemented(#name);          \
        return 0;                              \
    }
#define SPL_GPU_TRAP3(name)                             \
    int64_t name(int64_t a, int64_t b, int64_t c) {     \
        (void)a; (void)b; (void)c;                      \
        rt_trap_unimplemented(#name);                   \
        return 0;                                       \
    }

SPL_GPU_TRAP1(rt_gpu_global_id)
SPL_GPU_TRAP1(rt_gpu_global_size)
SPL_GPU_TRAP1(rt_gpu_group_id)
SPL_GPU_TRAP1(rt_gpu_local_id)
SPL_GPU_TRAP1(rt_gpu_local_size)
SPL_GPU_TRAP1(rt_gpu_num_groups)
SPL_GPU_TRAP0(rt_gpu_barrier)
SPL_GPU_TRAP0(rt_gpu_mem_fence)
SPL_GPU_TRAP1(rt_gpu_shared_alloc)
SPL_GPU_TRAP2(rt_gpu_atomic_add)
SPL_GPU_TRAP2(rt_gpu_atomic_add_i64)
SPL_GPU_TRAP2(rt_gpu_atomic_sub)
SPL_GPU_TRAP2(rt_gpu_atomic_sub_i64)
SPL_GPU_TRAP2(rt_gpu_atomic_and)
SPL_GPU_TRAP2(rt_gpu_atomic_and_i64)
SPL_GPU_TRAP2(rt_gpu_atomic_or)
SPL_GPU_TRAP2(rt_gpu_atomic_or_i64)
SPL_GPU_TRAP2(rt_gpu_atomic_xor)
SPL_GPU_TRAP2(rt_gpu_atomic_xor_i64)
SPL_GPU_TRAP2(rt_gpu_atomic_min)
SPL_GPU_TRAP2(rt_gpu_atomic_min_i64)
SPL_GPU_TRAP2(rt_gpu_atomic_max)
SPL_GPU_TRAP2(rt_gpu_atomic_max_i64)
SPL_GPU_TRAP2(rt_gpu_atomic_exchange)
SPL_GPU_TRAP2(rt_gpu_atomic_xchg_i64)
SPL_GPU_TRAP3(rt_gpu_atomic_cmpxchg_i64)

/* ==== Residual codegen-emitted entry points (2026-08-21) ==================
 * Closes the 45 names that check-no-unresolved-runtime-symbols.shs reported
 * as defined nowhere in the tree. Policy, unchanged from the block above:
 * never leave a codegen-emitted symbol undefined (a zero GOT slot SEGVs on
 * first call), never fabricate a value that silently corrupts, and where a
 * real implementation needs machinery the C runtime does not have (a work
 * scheduler, a coroutine stack, an interpreter), abort LOUDLY with the
 * symbol's own name via rt_trap_unimplemented.
 * Canonical semantics for the implemented ones are transcribed from
 * src/compiler_rust/runtime/src/value/{collections,objects}.rs. */

#define SPL_RT_TRAP1(name)                     \
    int64_t name(int64_t a) {                  \
        (void)a;                               \
        rt_trap_unimplemented(#name);          \
        return 0;                              \
    }
#define SPL_RT_TRAP2(name)                     \
    int64_t name(int64_t a, int64_t b) {       \
        (void)a; (void)b;                      \
        rt_trap_unimplemented(#name);          \
        return 0;                              \
    }
#define SPL_RT_TRAP3(name)                              \
    int64_t name(int64_t a, int64_t b, int64_t c) {     \
        (void)a; (void)b; (void)c;                      \
        rt_trap_unimplemented(#name);                   \
        return 0;                                       \
    }

/* ---- array (3): real semantics, collections.rs ------------------------- */

/* collections.rs:4770 -- first element, or nil on an empty/non-array. */
int64_t rt_array_first(int64_t array) {
    SplArray* a = (SplArray*)(intptr_t)array;
    if (a == NULL) return 0;
    if (rt_array_len(a) <= 0) return 0;
    return rt_array_get(a, 0);
}

/* collections.rs:5349 -- [[i, elem], ...]: one 2-element array per entry. */
int64_t rt_array_enumerate(int64_t array) {
    SplArray* a = (SplArray*)(intptr_t)array;
    SplArray* out;
    int64_t n, i;
    if (a == NULL) return 0;
    n = rt_array_len(a);
    out = rt_array_new(n > 0 ? n : 1);
    if (out == NULL) return 0;
    for (i = 0; i < n; i++) {
        SplArray* pair = rt_array_new(2);
        if (pair == NULL) break;
        rt_array_push(pair, i);
        rt_array_push(pair, rt_array_get(a, i));
        rt_array_push(out, (int64_t)(intptr_t)pair);
    }
    return (int64_t)(intptr_t)out;
}

/* collections.rs:1464 -- append `count` elements of src onto dst; true on ok. */
int8_t rt_array_extend_i64(int64_t dst, int64_t src, int64_t count) {
    SplArray* d = (SplArray*)(intptr_t)dst;
    SplArray* s = (SplArray*)(intptr_t)src;
    int64_t n, i;
    if (d == NULL || s == NULL) return 0;
    n = rt_array_len(s);
    if (count >= 0 && count < n) n = count;
    for (i = 0; i < n; i++) {
        if (!rt_array_push(d, rt_array_get(s, i))) return 0;
    }
    return 1;
}

/* ---- string (2): real semantics, collections.rs ------------------------ */

/* collections.rs:3895 -- split on '\n', dropping a single trailing empty. */
int64_t rt_string_lines(int64_t string) {
    int64_t nl = rt_string_new((const uint8_t*)"\n", 1);
    int64_t parts = rt_string_split(string, nl);
    SplArray* a = (SplArray*)(intptr_t)parts;
    int64_t n;
    if (a == NULL) return parts;
    n = rt_array_len(a);
    if (n > 0 && rt_string_len(rt_array_get(a, n - 1)) == 0) {
        /* Rust drops a single trailing empty line ("a\n" -> ["a"]). The C
         * SplArray has no pop-in-place primitive here, so rebuild without it. */
        SplArray* trimmed = rt_array_new(n - 1 > 0 ? n - 1 : 1);
        int64_t i;
        if (trimmed == NULL) return parts;
        for (i = 0; i < n - 1; i++) rt_array_push(trimmed, rt_array_get(a, i));
        return (int64_t)(intptr_t)trimmed;
    }
    return parts;
}

/* collections.rs:4239 -- Some(int) on a fully-numeric string, None otherwise. */
int64_t rt_string_parse_int(int64_t string) {
    int64_t len = rt_string_len(string);
    if (len <= 0) return rt_option_none();
    return rt_option_some(rt_string_to_int(string));
}

/* ---- unique / shared / handle (6): real semantics, objects.rs ----------
 * objects.rs boxes the value in a heap cell; the C runtime has no such cell
 * type, and the transparent identity box it would degrade to is exactly what
 * the Rust versions observably do for get(new(v)) == v. Ownership/refcount
 * tracking is NOT modelled -- recorded as a follow-up, not silently implied. */
int64_t rt_unique_new(int64_t value) { return value; }
int64_t rt_unique_get(int64_t unique) { return unique; }
int64_t rt_shared_new(int64_t value) { return value; }
int64_t rt_shared_get(int64_t shared) { return shared; }
int64_t rt_handle_new(int64_t value) { return value; }
int64_t rt_handle_get(int64_t handle) { return handle; }

/* ---- pointer (3): no Rust counterpart exists; emitter contract unknown -- */
SPL_RT_TRAP1(rt_pointer_new)
SPL_RT_TRAP1(rt_pointer_ref)
SPL_RT_TRAP1(rt_pointer_deref)

/* ---- vec / SIMD (13): value/simd.rs. Needs the SIMD vector heap object,
 * which the C runtime does not define; a scalar guess would silently compute
 * the wrong lanes. Named traps until the vector representation is ported. */
SPL_RT_TRAP3(rt_vec_blend)
SPL_RT_TRAP3(rt_vec_clamp)
SPL_RT_TRAP2(rt_vec_extract)
SPL_RT_TRAP3(rt_vec_fma)
SPL_RT_TRAP2(rt_vec_gather)
SPL_RT_TRAP2(rt_vec_load)
SPL_RT_TRAP3(rt_vec_masked_load)
SPL_RT_TRAP2(rt_vec_max_vec)
SPL_RT_TRAP2(rt_vec_min_vec)
SPL_RT_TRAP1(rt_vec_recip)
SPL_RT_TRAP3(rt_vec_select)
SPL_RT_TRAP2(rt_vec_shuffle)
SPL_RT_TRAP2(rt_vec_with)
SPL_RT_TRAP2(rt_neighbor_load)

/* ---- generator / future (4): need a coroutine stack + executor ---------- */
SPL_RT_TRAP2(rt_generator_create)
SPL_RT_TRAP1(rt_generator_next)
SPL_RT_TRAP2(rt_future_create)
SPL_RT_TRAP1(rt_future_await)

/* ---- par (3) / actor (3) / wait: need a work scheduler and mailboxes ---- */
SPL_RT_TRAP2(rt_par_map)
SPL_RT_TRAP2(rt_par_filter)
SPL_RT_TRAP3(rt_par_reduce)
SPL_RT_TRAP2(rt_actor_spawn)
SPL_RT_TRAP1(rt_actor_join)
int64_t rt_actor_recv(void) { rt_trap_unimplemented("rt_actor_recv"); return 0; }
SPL_RT_TRAP1(rt_wait)

/* ---- misc (4 remaining) ------------------------------------------------- */
/* Dynamic dispatch: the emitter passes no vtable identity the C runtime can
 * resolve, so any answer would be a wrong method address. */
SPL_RT_TRAP2(rt_vtable_lookup)
/* io_print.rs:437 takes (value, fmt_ptr, fmt_len) -- the format spec is a raw
 * pointer the C runtime cannot validate; naming the trap beats a wrong string. */
int64_t rt_value_format_string(int64_t v, const uint8_t* fmt, uint64_t fmt_len) {
    (void)v; (void)fmt; (void)fmt_len;
    rt_trap_unimplemented("rt_value_format_string");
    return 0;
}
SPL_RT_TRAP2(rt_fstring_format)
/* interpreter_bridge.rs:112 -- requires a hosted interpreter. */
SPL_RT_TRAP1(rt_interp_eval)

/* file_ops.rs:1344 -- write an i64 array as raw bytes. Real implementation. */
int8_t rt_file_write_bytes_array(int64_t path, int64_t data) {
    SplArray* a = (SplArray*)(intptr_t)data;
    int64_t n, i;
    unsigned char* buf;
    int8_t ok;
    if (a == NULL) return 0;
    n = rt_array_len(a);
    buf = (unsigned char*)malloc((size_t)(n > 0 ? n : 1));
    if (buf == NULL) return 0;
    for (i = 0; i < n; i++) buf[i] = (unsigned char)(rt_array_get(a, i) & 0xFF);
    {
        char* cpath = rt_core_string_to_cpath(path);
        if (cpath == NULL) { free(buf); return 0; }
        ok = (int8_t)(rt_file_write_bytes((const uint8_t*)cpath, (uint64_t)strlen(cpath),
                                          buf, (uint64_t)n) != 0);
        free(cpath);
    }
    free(buf);
    return ok;
}

/* collections.rs:1708 -- remove by key/index from array or dict. */
SPL_RT_TRAP2(rt_collection_remove)
