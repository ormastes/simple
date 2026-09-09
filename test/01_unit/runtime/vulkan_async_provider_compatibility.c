/* Provider ABI-v1 compatibility and async-extension admission, without a GPU.
 * Compile with dead stripping so unrelated hosted runtime entrypoints do not
 * need a complete language runtime. The actual production loader is included.
 */
#define dlopen fixture_dlopen
#define dlsym fixture_dlsym
#define dlclose fixture_dlclose
#include "../../../src/runtime/runtime_dynload.c"
#include <assert.h>
#include <stdio.h>

static int extension_kind;
static int missing_core;
static int created;
static int64_t query_abi(void) { return 1; }
static int64_t query_bits(void) { return 2; }
static int64_t query_async(void) { return 1; }
static int64_t fixture_create(int64_t capacity, int64_t timeout) {
    assert(capacity == 8 && timeout == 250000);
    ++created;
    return 91;
}
static int64_t unused_core(void) { return 0; }

void *fixture_dlopen(const char *path, int flags) {
    (void)path; (void)flags; return (void *)(uintptr_t)1;
}
int fixture_dlclose(void *handle) { (void)handle; return 0; }
void *fixture_dlsym(void *handle, const char *name) {
    (void)handle;
    if (!strcmp(name, "rt_simple_gpu_provider_abi_version")) return (void *)query_abi;
    if (!strcmp(name, "rt_simple_gpu_provider_backend_bits")) return (void *)query_bits;
    if (missing_core && !strcmp(name, "rt_vulkan_alloc_buffer")) return NULL;
    if (!strncmp(name, "rt_vulkan_async_session_", 24)) {
        if (!extension_kind) return NULL;
        if (extension_kind == 1 && !strcmp(name, "rt_vulkan_async_session_recover")) return NULL;
        if (!strcmp(name, "rt_vulkan_async_session_supported")) return (void *)query_async;
        if (!strcmp(name, "rt_vulkan_async_session_create_with_wait")) return (void *)fixture_create;
    }
    return (void *)unused_core;
}

int main(void) {
    SimpleGpuProviderState state = {SIMPLE_GPU_BACKEND_VULKAN, "unused", NULL, 0, 0, NULL, 0};
    setenv("SIMPLE_VULKAN_PROVIDER_PATH", "fixture-v1", 1);
    assert(simple_gpu_validate_surface(&state, (void *)(uintptr_t)1) == 1);
    assert(rt_vulkan_async_session_supported() == 0);
    assert(rt_vulkan_async_session_create_with_wait(8, 250000) == 0);
    assert(created == 0);
    extension_kind = 1;
    assert(rt_vulkan_async_session_supported() == 0);
    assert(rt_vulkan_async_session_create_with_wait(8, 250000) == 0);
    extension_kind = 2;
    assert(rt_vulkan_async_session_supported() == 1);
    assert(rt_vulkan_async_session_create_with_wait(8, 250000) == 91);
    assert(created == 1);
    missing_core = 1;
    assert(simple_gpu_validate_surface(&state, (void *)(uintptr_t)1) == 0);
    puts("PASS: legacy v1, absent/partial/full async extension, preserved core rejection");
    return 0;
}
