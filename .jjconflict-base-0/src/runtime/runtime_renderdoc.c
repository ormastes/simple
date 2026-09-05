/* Hosted RenderDoc in-application API (dlopen-based; no header/link dependency).
 *
 * RenderDoc's in-application API exposes exactly ONE real dynamic export:
 * RENDERDOC_GetAPI. Every other name (RENDERDOC_API_1_6_0's function-table
 * members) is reached only through the versioned table that GetAPI hands
 * back -- per-symbol dlsym of anything else binds NULL and is the macro/ABI
 * trap this shim exists to avoid. RenderDoc is normally already resident in
 * the process (injected by renderdoccmd / the Vulkan/GL capture layer), so
 * resolution tries RTLD_NOLOAD first and only falls back to a fresh dlopen.
 *
 * All ten rt_renderdoc_* entry points below report honest unavailability
 * (0 / empty text, never a fabricated handle or capture count) whenever the
 * library is absent, the one real export is missing, or GetAPI refuses the
 * requested version -- which is the normal path on a host with no RenderDoc
 * installed.
 */
#include "runtime.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#if defined(__linux__) || defined(__APPLE__)

#include <dlfcn.h>
#include <pthread.h>

typedef int (*RenderdocGetApiFn)(int version, void **out);

/* Offsets (in function-pointer slots) into the RENDERDOC_API_1_x_x table,
 * from renderdoc_app.h. The 1.0-compatible layout is stable across every
 * later minor version we could be handed. */
enum {
    RDOC_IDX_SET_CAPTURE_FILE_PATH_TEMPLATE = 11,
    RDOC_IDX_GET_NUM_CAPTURES = 13,
    RDOC_IDX_START_FRAME_CAPTURE = 19,
    RDOC_IDX_IS_FRAME_CAPTURING = 20,
    RDOC_IDX_END_FRAME_CAPTURE = 21
};

#define RDOC_API_VERSION_1_6_0 10600

static pthread_once_t g_renderdoc_once = PTHREAD_ONCE_INIT;
static const void **g_renderdoc_api = NULL; /* NULL = unresolved/unavailable */

static void renderdoc_resolve_once(void) {
    static const char *const names[] = {
        "librenderdoc.so",
        "build/tools/renderdoc/lib/librenderdoc.so",
        NULL
    };
    void *handle = NULL;
    for (size_t i = 0; names[i]; i++) {
        handle = dlopen(names[i], RTLD_NOW | RTLD_NOLOAD);
        if (handle) break;
    }
    if (!handle) {
        for (size_t i = 0; names[i]; i++) {
            handle = dlopen(names[i], RTLD_NOW | RTLD_LOCAL);
            if (handle) break;
        }
    }
    if (!handle) return; /* honest: librenderdoc.so is not present on this host */

    RenderdocGetApiFn get_api = (RenderdocGetApiFn)dlsym(handle, "RENDERDOC_GetAPI");
    if (!get_api) return; /* honest: the one real export is missing */

    void *api = NULL;
    int ok = get_api(RDOC_API_VERSION_1_6_0, &api);
    if (ok != 1 || !api) return; /* honest: GetAPI refused this version */

    g_renderdoc_api = (const void **)api;
}

static const void **renderdoc_api(void) {
    pthread_once(&g_renderdoc_once, renderdoc_resolve_once);
    return g_renderdoc_api;
}

static void *renderdoc_slot(int index) {
    const void **api = renderdoc_api();
    return api ? (void *)api[index] : NULL;
}

static void *renderdoc_device_ptr(int64_t device) {
    return device > 0 ? (void *)(intptr_t)device : NULL;
}

int64_t rt_renderdoc_available(void) {
    return renderdoc_api() != NULL ? 1 : 0;
}

int64_t rt_renderdoc_start_capture_for_device(int64_t device) {
    void *f = renderdoc_slot(RDOC_IDX_START_FRAME_CAPTURE);
    if (!f) return 0;
    ((void (*)(void *, void *))f)(renderdoc_device_ptr(device), NULL);
    return 1;
}

int64_t rt_renderdoc_start_capture(void) {
    return rt_renderdoc_start_capture_for_device(0);
}

int64_t rt_renderdoc_end_capture_for_device(int64_t device) {
    void *f = renderdoc_slot(RDOC_IDX_END_FRAME_CAPTURE);
    if (!f) return 0;
    return (int64_t)((uint32_t (*)(void *, void *))f)(renderdoc_device_ptr(device), NULL);
}

int64_t rt_renderdoc_end_capture(void) {
    return rt_renderdoc_end_capture_for_device(0);
}

int64_t rt_renderdoc_is_frame_capturing(void) {
    void *f = renderdoc_slot(RDOC_IDX_IS_FRAME_CAPTURING);
    if (!f) return 0;
    return (int64_t)((uint32_t (*)(void))f)();
}

int64_t rt_renderdoc_num_captures(void) {
    void *f = renderdoc_slot(RDOC_IDX_GET_NUM_CAPTURES);
    if (!f) return 0;
    return (int64_t)((uint32_t (*)(void))f)();
}

int64_t rt_renderdoc_set_capture_file_path_template(int64_t path_value) {
    void *f = renderdoc_slot(RDOC_IDX_SET_CAPTURE_FILE_PATH_TEMPLATE);
    if (!f) return 0;
    const char *path = rt_interp_cstr(path_value);
    if (!path) return 0;
    ((void (*)(const char *))f)(path);
    return 1;
}

int64_t rt_renderdoc_capture_file_path_template_from_env(void) {
    const char *value = getenv("RDOC_SIMPLE_CAPTURE_PATH");
    if (!value) value = "";
    return rt_string_new((const uint8_t *)value, (uint64_t)strlen(value));
}

int64_t rt_renderdoc_configure_capture_file_path_template_from_env(void) {
    const char *value = getenv("RDOC_SIMPLE_CAPTURE_PATH");
    if (!value || value[0] == '\0') return 0;
    void *f = renderdoc_slot(RDOC_IDX_SET_CAPTURE_FILE_PATH_TEMPLATE);
    if (!f) return 0;
    ((void (*)(const char *))f)(value);
    return 1;
}

#else

/* No dlopen-based RenderDoc support on this target yet: fail closed with the
 * same honest-unavailability contract as the Linux/macOS path above. */
int64_t rt_renderdoc_available(void) { return 0; }
int64_t rt_renderdoc_start_capture(void) { return 0; }
int64_t rt_renderdoc_start_capture_for_device(int64_t device) { (void)device; return 0; }
int64_t rt_renderdoc_end_capture(void) { return 0; }
int64_t rt_renderdoc_end_capture_for_device(int64_t device) { (void)device; return 0; }
int64_t rt_renderdoc_is_frame_capturing(void) { return 0; }
int64_t rt_renderdoc_num_captures(void) { return 0; }
int64_t rt_renderdoc_set_capture_file_path_template(int64_t path_value) { (void)path_value; return 0; }
int64_t rt_renderdoc_capture_file_path_template_from_env(void) { return rt_string_new(NULL, 0); }
int64_t rt_renderdoc_configure_capture_file_path_template_from_env(void) { return 0; }

#endif
