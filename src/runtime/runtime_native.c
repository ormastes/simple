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

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
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

bool rt_dir_create(const char* path, bool recursive) {
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
#define RT_CORE_ARRAY_FLAG_BYTES 0x08U
#define RT_CORE_ARRAY_FLAG_U64_PACKED 0x10U
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

int64_t rt_cuda_available(void) { return 0; }
int64_t rt_cuda_device_count(void) { return 0; }
int32_t rt_vk_available(void) { return 0; }
int64_t rt_vulkan_is_available(void) { return 0; }
int64_t rt_vulkan_device_count(void) { return 0; }

/* Optional hosted backends are unavailable in the core C runtime. */
#if defined(__GNUC__) || defined(__clang__)
#define SPL_HOSTED_UNAVAILABLE_WEAK __attribute__((weak))
#else
#define SPL_HOSTED_UNAVAILABLE_WEAK
#endif

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
SPL_HOSTED_UNAVAILABLE_WEAK void rt_sdl2_clear(int64_t handle, int64_t color) {
    (void)handle; (void)color;
}
SPL_HOSTED_UNAVAILABLE_WEAK void rt_sdl2_fill_rect(int64_t handle, int64_t x,
                                                    int64_t y, int64_t width,
                                                    int64_t height, int64_t color) {
    (void)handle; (void)x; (void)y; (void)width; (void)height; (void)color;
}
SPL_HOSTED_UNAVAILABLE_WEAK void rt_sdl2_present(int64_t handle) {
    (void)handle;
}

#if defined(SIMPLE_CORE_C_STANDALONE)
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

SPL_CORE_C_WEAK void rt_thread_sleep(int64_t millis) {
    rt_sleep_ms(millis);
}

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
const char* rt_host_gpu_queue_last_payload_text(void) { return rt_host_gpu_queue_last_payload_text_value; }

typedef struct RtCoreString {
    uint32_t kind;
    uint32_t reserved;
    uint64_t len;
    char data[];
} RtCoreString;

typedef struct RtCoreArray {
    uint8_t kind;
    uint8_t flags;
    uint8_t reserved[6];
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
    uint32_t enum_id;
    uint32_t discriminant;
    uint32_t reserved2;
    int64_t payload;
} RtCoreEnum;

typedef struct RtCoreClosure {
    uint8_t kind;
    uint8_t reserved[7];
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
    uint8_t reserved[6];
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
    uint32_t reserved;
    double value;
} RtCoreFloat;

static RtCoreDict* rt_core_as_dict(int64_t value);
static int64_t rt_core_dict_lookup(RtCoreDict* d, int64_t key);
static int rt_core_dict_put(RtCoreDict* d, int64_t key, int64_t value);
static int rt_core_dict_has(RtCoreDict* d, int64_t key);
static int rt_core_dict_del(RtCoreDict* d, int64_t key);

static RtCoreString** rt_core_string_registry = NULL;
static _Atomic size_t rt_core_heap_registry_count = 0;
static size_t rt_core_string_registry_len = 0;
static size_t rt_core_string_registry_cap = 0;
static RtCoreString* rt_core_short_string_cache[257] = {0};
static atomic_flag rt_core_short_string_cache_lock = ATOMIC_FLAG_INIT;
static RtCoreArray** rt_core_array_registry = NULL;
static size_t rt_core_array_registry_len = 0;
static size_t rt_core_array_registry_cap = 0;
static RtCoreEnum** rt_core_enum_registry = NULL;
static size_t rt_core_enum_registry_len = 0;
static size_t rt_core_enum_registry_cap = 0;
static RtCoreMutex** rt_core_mutex_registry = NULL;
static size_t rt_core_mutex_registry_len = 0;
static size_t rt_core_mutex_registry_cap = 0;
static atomic_flag rt_core_mutex_registry_lock = ATOMIC_FLAG_INIT;

static void rt_core_register_string(RtCoreString* s) {
    if (!s) return;
    if (rt_core_string_registry_len == rt_core_string_registry_cap) {
        size_t next_cap = rt_core_string_registry_cap == 0 ? 64 : rt_core_string_registry_cap * 2;
        RtCoreString** next = (RtCoreString**)realloc(rt_core_string_registry, next_cap * sizeof(RtCoreString*));
        if (!next) return;
        rt_core_string_registry = next;
        rt_core_string_registry_cap = next_cap;
    }
    rt_core_string_registry[rt_core_string_registry_len++] = s;
    atomic_fetch_add_explicit(&rt_core_heap_registry_count, 1, memory_order_relaxed);
}

static int rt_core_is_registered_string(RtCoreString* s) {
    for (size_t i = 0; i < rt_core_string_registry_len; i++) {
        if (rt_core_string_registry[i] == s) return 1;
    }
    return 0;
}

static void rt_core_register_array(RtCoreArray* array) {
    if (!array) return;
    if (rt_core_array_registry_len == rt_core_array_registry_cap) {
        size_t next_cap = rt_core_array_registry_cap == 0 ? 64 : rt_core_array_registry_cap * 2;
        RtCoreArray** next =
            (RtCoreArray**)realloc(rt_core_array_registry, next_cap * sizeof(RtCoreArray*));
        if (!next) return;
        rt_core_array_registry = next;
        rt_core_array_registry_cap = next_cap;
    }
    rt_core_array_registry[rt_core_array_registry_len++] = array;
    atomic_fetch_add_explicit(&rt_core_heap_registry_count, 1, memory_order_relaxed);
}

static int rt_core_is_registered_array(RtCoreArray* array) {
    for (size_t i = 0; i < rt_core_array_registry_len; i++) {
        if (rt_core_array_registry[i] == array) return 1;
    }
    return 0;
}

static int rt_core_unregister_array(RtCoreArray* array) {
    for (size_t i = 0; i < rt_core_array_registry_len; i++) {
        if (rt_core_array_registry[i] != array) continue;
        rt_core_array_registry[i] = rt_core_array_registry[--rt_core_array_registry_len];
        atomic_fetch_sub_explicit(&rt_core_heap_registry_count, 1, memory_order_relaxed);
        return 1;
    }
    return 0;
}

static void rt_core_register_mutex(RtCoreMutex* mutex) {
    if (!mutex) return;
    while (atomic_flag_test_and_set_explicit(&rt_core_mutex_registry_lock, memory_order_acquire)) { }
    if (rt_core_mutex_registry_len == rt_core_mutex_registry_cap) {
        size_t next_cap = rt_core_mutex_registry_cap == 0 ? 16 : rt_core_mutex_registry_cap * 2;
        RtCoreMutex** next = (RtCoreMutex**)realloc(rt_core_mutex_registry, next_cap * sizeof(RtCoreMutex*));
        if (!next) {
            atomic_flag_clear_explicit(&rt_core_mutex_registry_lock, memory_order_release);
            return;
        }
        rt_core_mutex_registry = next;
        rt_core_mutex_registry_cap = next_cap;
    }
    rt_core_mutex_registry[rt_core_mutex_registry_len++] = mutex;
    atomic_fetch_add_explicit(&rt_core_heap_registry_count, 1, memory_order_relaxed);
    atomic_flag_clear_explicit(&rt_core_mutex_registry_lock, memory_order_release);
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
 * or otherwise) are unaffected since they are always registered at creation. */
static void rt_core_register_enum(RtCoreEnum* e) {
    if (!e) return;
    if (rt_core_enum_registry_len == rt_core_enum_registry_cap) {
        size_t next_cap = rt_core_enum_registry_cap == 0 ? 64 : rt_core_enum_registry_cap * 2;
        RtCoreEnum** next = (RtCoreEnum**)realloc(rt_core_enum_registry, next_cap * sizeof(RtCoreEnum*));
        if (!next) return;
        rt_core_enum_registry = next;
        rt_core_enum_registry_cap = next_cap;
    }
    rt_core_enum_registry[rt_core_enum_registry_len++] = e;
    atomic_fetch_add_explicit(&rt_core_heap_registry_count, 1, memory_order_relaxed);
}

static int rt_core_is_registered_enum(RtCoreEnum* e) {
    for (size_t i = 0; i < rt_core_enum_registry_len; i++) {
        if (rt_core_enum_registry[i] == e) return 1;
    }
    return 0;
}

static RtCoreClosure** rt_core_closure_registry = NULL;
static size_t rt_core_closure_registry_len = 0;
static size_t rt_core_closure_registry_cap = 0;
static atomic_flag rt_core_closure_registry_lock = ATOMIC_FLAG_INIT;

int64_t rt_heap_registry_count(void) {
    return (int64_t)atomic_load_explicit(&rt_core_heap_registry_count, memory_order_relaxed);
}

static void rt_core_closure_registry_acquire(void) {
    while (atomic_flag_test_and_set_explicit(&rt_core_closure_registry_lock, memory_order_acquire)) {}
}

static void rt_core_closure_registry_release(void) {
    atomic_flag_clear_explicit(&rt_core_closure_registry_lock, memory_order_release);
}

static int rt_core_register_closure(RtCoreClosure* closure) {
    if (!closure) return 0;
    rt_core_closure_registry_acquire();
    if (rt_core_closure_registry_len == rt_core_closure_registry_cap) {
        if (rt_core_closure_registry_cap > SIZE_MAX / 2 / sizeof(RtCoreClosure*)) {
            rt_core_closure_registry_release();
            return 0;
        }
        size_t next_cap = rt_core_closure_registry_cap == 0 ? 32 : rt_core_closure_registry_cap * 2;
        RtCoreClosure** next =
            (RtCoreClosure**)realloc(rt_core_closure_registry, next_cap * sizeof(RtCoreClosure*));
        if (!next) {
            rt_core_closure_registry_release();
            return 0;
        }
        rt_core_closure_registry = next;
        rt_core_closure_registry_cap = next_cap;
    }
    rt_core_closure_registry[rt_core_closure_registry_len++] = closure;
    atomic_fetch_add_explicit(&rt_core_heap_registry_count, 1, memory_order_relaxed);
    rt_core_closure_registry_release();
    return 1;
}

static RtCoreClosure* rt_core_as_closure(int64_t value) {
    if ((((uint64_t)value) & RT_VALUE_TAG_MASK) != RT_VALUE_TAG_HEAP) return NULL;
    RtCoreClosure* closure = (RtCoreClosure*)(uintptr_t)(((uint64_t)value) & ~RT_VALUE_TAG_MASK);
    if (!closure) return NULL;
    /* Membership is a pointer-only comparison. Do not dereference a raw
     * function pointer that merely collides with the heap tag. */
    rt_core_closure_registry_acquire();
    for (size_t i = 0; i < rt_core_closure_registry_len; i++) {
        if (rt_core_closure_registry[i] == closure) {
            RtCoreClosure* result = closure->kind == RT_VALUE_HEAP_CLOSURE ? closure : NULL;
            rt_core_closure_registry_release();
            return result;
        }
    }
    rt_core_closure_registry_release();
    return NULL;
}

/* ----------------------------------------------------------------------------
 * Heap-boxed float registry (O(1) discrimination).
 *
 * The existing string/enum/closure/mutex registries above are LINEAR SCANS,
 * fine because those objects are relatively few. Container floats are numerous,
 * so a linear registry would make float discrimination O(n) per check and the
 * whole program O(n^2). This is instead an open-addressing HashSet of registered
 * RtCoreFloat pointers: register-on-alloc, O(1) amortized membership. Membership
 * is a pure pointer comparison performed BEFORE any dereference, so a flat i64
 * that merely aliases RT_VALUE_TAG_HEAP (see the tag-collision SEGV note above
 * rt_core_register_enum) is never dereferenced -- it simply isn't a member.
 *
 * Leak model: entries are never removed. Heap-floats live for the process
 * lifetime (no-GC: arrays/dicts free their backing buffer but not the tagged
 * element values), exactly like the transient short strings above, so their
 * addresses are never reused and stale-membership false positives cannot occur.
 * -------------------------------------------------------------------------- */
static uintptr_t* rt_core_float_registry = NULL; /* open-addressing table, 0 = empty */
static size_t rt_core_float_registry_cap = 0;    /* power of two, or 0 */
static size_t rt_core_float_registry_len = 0;
static atomic_flag rt_core_float_registry_lock = ATOMIC_FLAG_INIT;

static void rt_core_float_registry_acquire(void) {
    while (atomic_flag_test_and_set_explicit(&rt_core_float_registry_lock, memory_order_acquire)) {}
}
static void rt_core_float_registry_release(void) {
    atomic_flag_clear_explicit(&rt_core_float_registry_lock, memory_order_release);
}

static inline size_t rt_core_float_hash_ptr(uintptr_t p) {
    uint64_t x = (uint64_t)p;
    x ^= x >> 33;
    x *= 0xff51afd7ed558ccdULL;
    x ^= x >> 33;
    return (size_t)x;
}

/* caller holds the lock; table has a free slot */
static void rt_core_float_registry_insert_raw(uintptr_t p) {
    size_t mask = rt_core_float_registry_cap - 1;
    size_t i = rt_core_float_hash_ptr(p) & mask;
    for (;;) {
        if (rt_core_float_registry[i] == 0) {
            rt_core_float_registry[i] = p;
            rt_core_float_registry_len++;
            return;
        }
        if (rt_core_float_registry[i] == p) return; /* already present */
        i = (i + 1) & mask;
    }
}

/* caller holds the lock */
static int rt_core_float_registry_grow(void) {
    size_t new_cap = rt_core_float_registry_cap == 0 ? 256 : rt_core_float_registry_cap * 2;
    if (new_cap > SIZE_MAX / sizeof(uintptr_t)) return 0;
    uintptr_t* fresh = (uintptr_t*)calloc(new_cap, sizeof(uintptr_t));
    if (!fresh) return 0;
    uintptr_t* old = rt_core_float_registry;
    size_t old_cap = rt_core_float_registry_cap;
    rt_core_float_registry = fresh;
    rt_core_float_registry_cap = new_cap;
    rt_core_float_registry_len = 0;
    for (size_t i = 0; i < old_cap; i++) {
        if (old[i] != 0) rt_core_float_registry_insert_raw(old[i]);
    }
    free(old);
    return 1;
}

static void rt_core_register_float(RtCoreFloat* f) {
    if (!f) return;
    rt_core_float_registry_acquire();
    /* grow at 70% load */
    if ((rt_core_float_registry_len + 1) * 10 >= rt_core_float_registry_cap * 7) {
        if (!rt_core_float_registry_grow()) {
            rt_core_float_registry_release();
            return;
        }
    }
    rt_core_float_registry_insert_raw((uintptr_t)f);
    atomic_fetch_add_explicit(&rt_core_heap_registry_count, 1, memory_order_relaxed);
    rt_core_float_registry_release();
}

static int rt_core_is_registered_float(RtCoreFloat* f) {
    if (!f) return 0;
    int found = 0;
    rt_core_float_registry_acquire();
    if (rt_core_float_registry_cap != 0) {
        size_t mask = rt_core_float_registry_cap - 1;
        size_t i = rt_core_float_hash_ptr((uintptr_t)f) & mask;
        for (;;) {
            uintptr_t e = rt_core_float_registry[i];
            if (e == 0) break;
            if (e == (uintptr_t)f) { found = 1; break; }
            i = (i + 1) & mask;
        }
    }
    rt_core_float_registry_release();
    return found;
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
        return (int64_t)(raw >> 3);
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

static inline RtCoreArray* rt_core_as_array(int64_t value) {
    uintptr_t raw = (uintptr_t)value;
    if (raw < 4096) return NULL;
    if ((raw & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_HEAP) {
        raw &= ~RT_VALUE_TAG_MASK;
    } else if ((raw & RT_VALUE_TAG_MASK) != 0) {
        return NULL;
    }
    RtCoreArray* a = (RtCoreArray*)raw;
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

static int8_t rt_core_array_reserve(SplArray* a, int64_t min_cap);

static void rt_core_write_bytes(FILE* stream, const uint8_t* ptr, uint64_t len) {
    if (!ptr || len == 0) return;
    fwrite(ptr, 1, (size_t)len, stream);
}

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

int64_t rt_value_int(int64_t value) {
    return (int64_t)(((uint64_t)value << 3) | RT_VALUE_TAG_INT);
}

int64_t rt_value_as_int(int64_t value) {
    return value >> 3;
}

/* Box an f64 (passed as its raw i64 bit pattern) into the tagged RuntimeValue
 * representation. Floats are HEAP-BOXED (lossless): the old inline TAG_FLOAT
 * form kept only (bits & ~7), zeroing the low 3 mantissa bits, so a container/Any
 * float lost precision. We allocate an RtCoreFloat leaf holding the full double
 * and return a TAG_HEAP pointer. Scalar/arithmetic f64 held in native registers
 * never reaches here -- only values that enter the tagged representation box. */
int64_t rt_value_float(int64_t raw_bits) {
    RtCoreFloat* f = (RtCoreFloat*)malloc(sizeof(RtCoreFloat));
    if (!f) {
        /* OOM: fall back to the legacy lossy inline form rather than crash. */
        return (int64_t)(((uint64_t)raw_bits & ~RT_VALUE_TAG_MASK) | RT_VALUE_TAG_FLOAT);
    }
    f->kind = RT_VALUE_HEAP_FLOAT;
    f->reserved = 0;
    memcpy(&f->value, &raw_bits, sizeof(f->value));
    rt_core_register_float(f);
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

static int64_t rt_string_new_uncached(const uint8_t* bytes, uint64_t len) {
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
    rt_core_register_string(s);
    return (int64_t)(((uint64_t)(uintptr_t)s) | RT_VALUE_TAG_HEAP);
}

int64_t rt_string_new(const uint8_t* bytes, uint64_t len) {
    if (!bytes && len > 0) return rt_core_nil();
    if (len > 1) return rt_string_new_uncached(bytes, len);

    size_t index = len == 0 ? 0 : (size_t)bytes[0] + 1;
    while (atomic_flag_test_and_set_explicit(&rt_core_short_string_cache_lock, memory_order_acquire)) { }
    RtCoreString* cached = rt_core_short_string_cache[index];
    if (!cached) {
        int64_t value = rt_string_new_uncached(bytes, len);
        cached = rt_core_as_string(value);
        if (cached) rt_core_short_string_cache[index] = cached;
    }
    atomic_flag_clear_explicit(&rt_core_short_string_cache_lock, memory_order_release);
    return cached
        ? (int64_t)(((uint64_t)(uintptr_t)cached) | RT_VALUE_TAG_HEAP)
        : rt_core_nil();
}

int64_t rt_string_len(int64_t string) {
    RtCoreString* s = rt_core_as_string(string);
    return s ? (int64_t)s->len : -1;
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
        else if (lead >= 0xf0 && lead <= 0xf7 && i + 4 <= s->len) width = 4;
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
 * terminated buffer; anything else is assumed to already be a raw char* and
 * is passed through. Used by MIR StringLit interpolation lowering, which then
 * concatenates the raw segments with rt_strcat. Uses the same rt_core_as_string
 * accessor + s->data buffer as rt_string_data above. */
const char* rt_interp_cstr(int64_t v) {
    RtCoreString* s = rt_core_as_string(v);
    return s ? (const char*)s->data : (const char*)(uintptr_t)v;
}

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

    uint64_t len = a->len + b->len;
    RtCoreString* out = (RtCoreString*)malloc(sizeof(RtCoreString) + (size_t)len + 1);
    if (!out) return rt_core_nil();
    out->kind = RT_VALUE_HEAP_STRING;
    out->reserved = 0;
    out->len = len;
    if (a->len > 0) memcpy(out->data, a->data, (size_t)a->len);
    if (b->len > 0) memcpy(out->data + a->len, b->data, (size_t)b->len);
    out->data[len] = '\0';
    rt_core_register_string(out);
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

int64_t rt_to_string(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (s) return value;

    char buf[64];
    if (rt_core_is_int(value)) {
        int64_t n = (int64_t)((uint64_t)value >> 3);
        int len = snprintf(buf, sizeof(buf), "%lld", (long long)n);
        return rt_string_new((const uint8_t*)buf, len > 0 ? (uint64_t)len : 0);
    }
    if (rt_core_is_float(value)) {
        uint64_t bits = ((uint64_t)value) & ~RT_VALUE_TAG_MASK;
        double f;
        memcpy(&f, &bits, sizeof(f));
        int len = snprintf(buf, sizeof(buf), "%.17g", f);
        return rt_string_new((const uint8_t*)buf, len > 0 ? (uint64_t)len : 0);
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
 * (16 3's). rt_to_string()'s existing tagged/boxed-ANY float path uses raw
 * %.17g (0.1 -> "0.10000000000000001") and does NOT match -- do not reuse it.
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
    return rt_core_is_int(value) && rt_core_as_int(value) == expected;
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
    if (left == right) return 1;
    const char* a = rt_interp_cstr(left);
    const char* b = rt_interp_cstr(right);
    if (a == b) return 1;
    if (!a || !b) return 0;
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
        rt_core_register_string(out);
        return (int64_t)(((uint64_t)(uintptr_t)out) | RT_VALUE_TAG_HEAP);
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
    if (!s || !n || start < 0) return -1;
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
    rt_core_register_mutex(mutex);
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

static int64_t rt_string_ascii_case(int64_t value, int to_lower) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) return rt_core_nil();
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
    rt_core_register_string(out);
    return (int64_t)(((uint64_t)(uintptr_t)out) | RT_VALUE_TAG_HEAP);
}

int64_t rt_string_to_lower(int64_t value) {
    return rt_string_ascii_case(value, 1);
}

int64_t rt_string_to_upper(int64_t value) {
    return rt_string_ascii_case(value, 0);
}

/* parse_f64 (native_string_methods_unresolved_in_mir lane, 2026-07-18):
 * `.parse_f64()` had no native runtime counterpart at all -- unlike
 * to_lower/to_upper (which already had this C implementation before this
 * lane; only their MIR dispatch arm was missing), string->f64 parsing was
 * entirely absent from the native runtime. Mirrors the tagged-string-in
 * family: rt_core_as_string unboxes the tagged handle the MIR call site
 * already produces via ensure_tagged_str, and RtCoreString.data is always
 * NUL-terminated (see rt_string_new), so strtod can read it directly.
 * strtod matches the oracle's Rust `str::parse::<f64>()` for well-formed
 * decimal literals (both are correctly-rounded decimal->binary conversions).
 * Returns 0.0 for a nil/unparseable receiver -- the same "bare-payload
 * sentinel" shortcut already used by rfind (-1 for not-found instead of a
 * real Option<i64>), since this lowering mode has no Option<f64> boxing on
 * the native path; revisit if a closure site ever needs to distinguish a
 * genuine 0.0 parse from a parse failure. */
double rt_string_parse_f64(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) return 0.0;
    return strtod(s->data, NULL);
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
    rt_core_register_string(out);
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
    if (rt_enum_discriminant(value) >= 0) return rt_enum_payload(value);
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
    rt_core_register_string(out);
    return (int64_t)(((uint64_t)(uintptr_t)out) | RT_VALUE_TAG_HEAP);
}

int64_t rt_string_trim(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) return value;
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
    if (!s) return value;
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
    if (!s) return value;
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

void rt_set_args(int argc, char** argv) {
    spl_init_args(argc, argv);
}

int32_t rt_get_argc(void) {
    return (int32_t)spl_arg_count();
}

SplArray* rt_get_args(void) {
    return rt_cli_get_args();
}

SplArray* rt_cli_get_args(void) {
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

int64_t rt_cli_arg_count(void) {
    return spl_arg_count();
}

int64_t rt_cli_arg_at(int64_t index) {
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

void* rt_alloc(int64_t size) {
    return malloc((size_t)size);
}

void* rt_realloc(void* ptr, int64_t size) {
    return realloc(ptr, (size_t)size);
}

void rt_free(void* ptr) {
    free(ptr);
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
    rt_core_register_string(out);
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
    rt_core_register_array(a);
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

void rt_array_set(SplArray* a, int64_t idx, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return;
    if (idx < 0) idx = array->len + idx;
    if (idx < 0 || idx >= array->len) return;
    if (array->flags & RT_CORE_ARRAY_FLAG_BYTES) {
        ((uint8_t*)array->data)[idx] = (uint8_t)(rt_core_numeric_arg(val) & 0xff);
    } else {
        ((int64_t*)array->data)[idx] = val;
    }
}

int8_t rt_array_set_text(SplArray* a, int64_t idx, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    rt_array_set(a, idx, val);
    return 1;
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

int8_t rt_array_clear(SplArray* a) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    array->len = 0;
    return 1;
}

int8_t rt_array_push_i64_raw(SplArray* a, int64_t val) {
    return rt_array_push(a, val);
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

int64_t rt_array_data_ptr_u8(SplArray* a) {
    return rt_array_data_ptr(a);
}

static char* rt_core_string_to_cstring(int64_t value) {
    RtCoreString* string = rt_core_as_string(value);
    if (!string || string->len > SIZE_MAX - 1) return NULL;
    char* out = (char*)malloc((size_t)string->len + 1);
    if (!out) return NULL;
    memcpy(out, string->data, (size_t)string->len);
    out[string->len] = '\0';
    return out;
}

int64_t spl_dlopen(int64_t path_value) {
    char* path = rt_core_string_to_cstring(path_value);
    if (!path) return 0;
#if defined(_WIN32)
    void* handle = (void*)LoadLibraryA(path);
#else
    void* handle = dlopen(path, RTLD_NOW);
#endif
    free(path);
    return (int64_t)(uintptr_t)handle;
}

int64_t spl_dlsym(int64_t handle_value, int64_t name_value) {
    char* name = rt_core_string_to_cstring(name_value);
    if (!name) return 0;
#if defined(_WIN32)
    void* symbol = handle_value == 0 ? NULL : (void*)GetProcAddress((HMODULE)(uintptr_t)handle_value, name);
#else
    void* symbol = dlsym((void*)(uintptr_t)handle_value, name);
#endif
    free(name);
    return (int64_t)(uintptr_t)symbol;
}

int64_t spl_dlclose(int64_t handle_value) {
    if (handle_value == 0) return 0;
#if defined(_WIN32)
    return FreeLibrary((HMODULE)(uintptr_t)handle_value) ? 0 : 1;
#else
    return (int64_t)dlclose((void*)(uintptr_t)handle_value);
#endif
}

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
    return (array->flags & RT_CORE_ARRAY_FLAG_U64_PACKED) ? value : rt_core_as_int(value);
}

int8_t rt_typed_words_u64_push(SplArray* a, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    if (!rt_core_array_reserve(a, array->len + 1)) return 0;
    ((int64_t*)array->data)[array->len++] =
        (array->flags & RT_CORE_ARRAY_FLAG_U64_PACKED) ? val : rt_value_int(val);
    return 1;
}

int8_t rt_typed_words_u64_set(SplArray* a, int64_t idx, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    if (idx < 0) idx = array->len + idx;
    if (idx < 0 || idx >= array->len) return 0;
    ((int64_t*)array->data)[idx] =
        (array->flags & RT_CORE_ARRAY_FLAG_U64_PACKED) ? val : rt_value_int(val);
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
        (array->flags & RT_CORE_ARRAY_FLAG_U64_PACKED) ? val : rt_value_int(val);
    return 1;
}

int64_t rt_tuple_new(int64_t len) {
    SplArray* tuple = rt_array_new(len);
    if (!tuple) return rt_core_nil();
    RtCoreArray* array = rt_core_array_ptr(tuple);
    if (!array) return rt_core_nil();
    array->len = len < 0 ? 0 : len;
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
    for (int i = 0; i < rt_enum_intern_count; i++) {
        if (rt_enum_intern_table[i].enum_id == enum_id &&
            rt_enum_intern_table[i].discriminant == discriminant &&
            rt_enum_intern_table[i].payload == payload) {
            return rt_enum_intern_table[i].value;
        }
    }
    RtCoreEnum* value = (RtCoreEnum*)calloc(1, sizeof(RtCoreEnum));
    if (!value) return rt_core_nil();
    value->kind = RT_VALUE_HEAP_ENUM;
    value->enum_id = (uint32_t)enum_id;
    value->discriminant = (uint32_t)discriminant;
    value->payload = payload;
    rt_core_register_enum(value);
    int64_t tagged = (int64_t)(((uint64_t)(uintptr_t)value) | RT_VALUE_TAG_HEAP);
    if (rt_enum_intern_count < RT_ENUM_INTERN_MAX) {
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

static RtCoreDict* rt_core_as_dict(int64_t value) {
    uintptr_t raw = (uintptr_t)value;
    if (raw < 4096) return NULL;
    if ((raw & RT_VALUE_TAG_MASK) != RT_VALUE_TAG_HEAP) return NULL;
    RtCoreDict* d = (RtCoreDict*)(raw & ~RT_VALUE_TAG_MASK);
    if (!d || d->kind != RT_VALUE_HEAP_DICT) return NULL;
    return d;
}

/* Canonicalize a key so that the raw-int form produced by `d[k] = v` (IndexSet,
 * unboxed) and the tagged form produced by `d.get(k)` (method path, rt_box_int)
 * collapse to one representation. String/heap keys are kept as-is and matched by
 * content via rt_native_eq. */
static int64_t rt_core_dict_canon_key(int64_t k) {
    if (rt_core_as_string(k)) return k;
    /* A heap-boxed float key is a fresh pointer per value, so two keys of the
     * same double would land in different buckets. Canonicalize to the inline
     * tagged form (value-based, -0.0 normalized to 0.0) so equal-valued float
     * keys collapse to one key -- the same identity float dict keys had before
     * heap-boxing (keys keep the pre-existing low-3-bit fold; dict VALUES are
     * lossless via the heap box). */
    RtCoreFloat* f = rt_core_as_heap_float(k);
    if (f) {
        double d = f->value;
        if (d == 0.0) d = 0.0; /* fold -0.0 -> +0.0 so both zeros hash alike */
        uint64_t bits;
        memcpy(&bits, &d, sizeof(bits));
        return (int64_t)((bits & ~RT_VALUE_TAG_MASK) | RT_VALUE_TAG_FLOAT);
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
    uint64_t x = (uint64_t)k;
    x ^= x >> 33;
    x *= 0xff51afd7ed558ccdULL;
    x ^= x >> 33;
    return x;
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
        } else if (e->hash == h && rt_native_eq(e->key, ck)) {
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
        if (e->occupied == 1 && e->hash == h && rt_native_eq(e->key, ck)) return e->value;
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
        if (e->occupied == 1 && e->hash == h && rt_native_eq(e->key, ck)) return 1;
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
        if (e->occupied == 1 && e->hash == h && rt_native_eq(e->key, ck)) {
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
    return collection;
}

/* ================================================================
 * File I/O (wrappers around existing rt_/spl_ functions)
 * ================================================================ */

/* rt_file_read_text, rt_file_exists, rt_file_delete, rt_env_get are
 * defined in runtime.c when the full runtime is linked, but the
 * core-c-bootstrap build only includes runtime_legacy_core.c and
 * runtime_mcp_core.c (not runtime.c).  Provide them here so that
 * native CLI binaries built against the core-c runtime can read files
 * and query the environment without segfaulting on nil stubs. */

static char* rt_core_string_to_cpath(int64_t value);

const char* rt_file_read_text(const char* path) {
    return spl_file_read(path);
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

int rt_file_exists(const char* path) {
    if (!path) return 0;
    FILE* f = fopen(path, "r");
    if (f) { fclose(f); return 1; }
    return 0;
}

int rt_file_delete(const char* path) {
    if (!path) return 0;
    return remove(path) == 0 ? 1 : 0;
}

int rt_file_remove(int64_t path_value, int64_t path_len_unused) {
    (void)path_len_unused;
    char* path = rt_core_string_to_cpath(path_value);
    if (!path) return 0;
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

int64_t rt_file_size(const char* path) {
    if (!path) return -1;
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

int64_t rt_env_get(const uint8_t* key_ptr, uint64_t key_len) {
    char* key = rt_core_text_arg_to_cstr(key_ptr, key_len);
    if (!key) return rt_core_nil();
    const char* value = getenv(key);
    free(key);
    if (!value) return rt_core_nil();
    return rt_string_new((const uint8_t*)value, (uint64_t)strlen(value));
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
        if (!rt_dir_exists(parent) && !rt_dir_create(parent, true)) {
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

void* rt_file_open(const char* path, const char* mode) {
    if (!path || !mode) return NULL;
    return (void*)fopen(path, mode);
}

void rt_file_close(void* handle) {
    if (handle) fclose((FILE*)handle);
}

int rt_file_move(const char* src, const char* dst) {
    if (!src || !dst) return 0;
    return rename(src, dst) == 0 ? 1 : 0;
}

char* rt_env_cwd(void) {
    return rt_getcwd();
}

const char* rt_platform_name(void) {
#if defined(_WIN32)
    return "windows";
#elif defined(__APPLE__)
    return "macos";
#elif defined(__FreeBSD__)
    return "freebsd";
#elif defined(__linux__)
    return "linux";
#elif defined(__illumos__)
    return "illumos";
#elif defined(__sun) && defined(__SVR4)
    return "solaris";
#else
    return "unknown";
#endif
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

int rt_dir_create_all(const char* path) {
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

int rt_mkdir_p(const char* path) {
    return rt_dir_create_all(path);
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

SplArray* rt_process_run(const char* cmd, uint64_t cmd_len, SplArray* args) {
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

int64_t* rt_process_run_tuple(int64_t cmd, SplArray* args) {
    const char* cmd_c = rt_interp_cstr(cmd);
    uint64_t cmd_len = cmd_c ? (uint64_t)strlen(cmd_c) : 0;
    return rt_process_result_to_tuple(rt_process_run(cmd_c ? cmd_c : "", cmd_len, args));
}

int64_t* rt_process_run_timeout_tuple(int64_t cmd, SplArray* args, int64_t timeout_ms) {
    const char* cmd_c = rt_interp_cstr(cmd);
    uint64_t cmd_len = cmd_c ? (uint64_t)strlen(cmd_c) : 0;
    return rt_process_result_to_tuple(
        rt_process_run_timeout(cmd_c ? cmd_c : "", cmd_len, args, timeout_ms));
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

SplArray* rt_bytes_from_raw(int64_t ptr, int64_t len) {
    /* Create a byte array ([u8]) from a raw memory pointer.
     * Used by LLVM memory buffer emission to avoid temp file I/O. */
    if (ptr == 0 || len <= 0) return rt_byte_array_new_len(0);
    SplArray* result = rt_byte_array_new_len((uint64_t)len);
    RtCoreArray* array = rt_core_array_ptr(result);
    if (!array || !array->data) return result;
    memcpy(array->data, (const void*)(uintptr_t)ptr, (size_t)len);
    return result;
}

/* ================================================================
 * Directory Operations (bridge to spl_ or direct libc)
 * ================================================================ */

/* rt_dir_create is already in runtime.h (takes path + recursive) but
 * LLVM IR declares it as rt_dir_create(ptr) -> i1 (single arg).
 * Provide the single-arg version. */
int rt_dir_delete(const char* path) {
    return rt_dir_remove_all(path) ? 1 : 0;
}

int rt_dir_exists(const char* path) {
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

int64_t rt_time_now_monotonic_ms(void) {
    return rt_time_now_micros() / 1000LL;
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
    int64_t* ptr = (int64_t*)((char*)(uintptr_t)addr + offset);
    return *ptr;
}

void rt_ptr_write_u8(int64_t addr, int64_t offset, int64_t value) {
    uint8_t* ptr = (uint8_t*)((char*)(uintptr_t)addr + offset);
    *ptr = (uint8_t)value;
}

void rt_ptr_write_i32(int64_t addr, int64_t offset, int32_t value) {
    int32_t* ptr = (int32_t*)((char*)(uintptr_t)addr + offset);
    *ptr = value;
}

void rt_ptr_write_i64(int64_t addr, int64_t offset, int64_t value) {
    int64_t* ptr = (int64_t*)((char*)(uintptr_t)addr + offset);
    *ptr = value;
}

/* ================================================================
 * Error Handling
 * ================================================================ */

void rt_panic(const char* msg) {
    spl_panic(msg);
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

void rt_channel_send(int64_t id, int64_t value) {
    if (id < 0 || id >= RT_CHAN_MAX) return;
    RtChannel* ch = &rt_channels[id];
    if (!ch->in_use || ch->closed) return;
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
void rt_channel_send(int64_t id, int64_t v) { (void)id; (void)v; }
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
