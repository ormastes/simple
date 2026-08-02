/* Narrow CUDA Driver API ABI shim for the pure-Simple audio offload owner.
 * Policy, lifecycle state, validation, scheduling, and parity stay in Simple;
 * this file only adapts CUDA out-parameters and the 11-argument launch ABI. */
#include <dlfcn.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

typedef int (*cu_init_fn)(unsigned int);
typedef int (*cu_device_count_fn)(int *);
typedef int (*cu_device_get_fn)(int *, int);
typedef int (*cu_ctx_create_fn)(void **, unsigned int, int);
typedef int (*cu_ctx_destroy_fn)(void *);
typedef int (*cu_module_load_fn)(void **, const void *);
typedef int (*cu_module_unload_fn)(void *);
typedef int (*cu_module_get_fn)(void **, void *, const char *);
typedef int (*cu_mem_alloc_fn)(uint64_t *, size_t);
typedef int (*cu_mem_free_fn)(uint64_t);
typedef int (*cu_copy_htod_fn)(uint64_t, const void *, size_t);
typedef int (*cu_copy_dtoh_fn)(void *, uint64_t, size_t);
typedef int (*cu_sync_fn)(void);
typedef int (*cu_launch_fn)(void *, unsigned int, unsigned int, unsigned int,
    unsigned int, unsigned int, unsigned int, unsigned int, void *, void **, void **);

struct simple_audio_cuda {
    void *library;
    void *context;
    int device;
    cu_ctx_destroy_fn ctx_destroy;
    cu_module_load_fn module_load;
    cu_module_unload_fn module_unload;
    cu_module_get_fn module_get;
    cu_mem_alloc_fn mem_alloc;
    cu_mem_free_fn mem_free;
    cu_copy_htod_fn copy_htod;
    cu_copy_dtoh_fn copy_dtoh;
    cu_sync_fn sync;
    cu_launch_fn launch;
};

static size_t simple_audio_host_mapping_size;

int64_t simple_audio_host_map_shared(int64_t path_raw) {
    const char *path = (const char *)(uintptr_t)path_raw;
    if (!path) return 0;
    int fd = open(path, O_RDWR);
    if (fd < 0) return 0;
    struct stat info;
    if (fstat(fd, &info) != 0 || info.st_size <= 0) {
        close(fd);
        return 0;
    }
    simple_audio_host_mapping_size = (size_t)info.st_size;
    void *mapped = mmap(NULL, simple_audio_host_mapping_size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    close(fd);
    if (mapped == MAP_FAILED) {
        simple_audio_host_mapping_size = 0;
        return 0;
    }
    return (int64_t)(uintptr_t)mapped;
}

int64_t simple_audio_host_unmap_shared(int64_t address) {
    if (!address || simple_audio_host_mapping_size == 0) return 0;
    int result = munmap((void *)(uintptr_t)address, simple_audio_host_mapping_size) == 0 ? 1 : 0;
    simple_audio_host_mapping_size = 0;
    return result;
}

static void *symbol(void *library, const char *primary, const char *fallback) {
    void *value = dlsym(library, primary);
    return value ? value : (fallback ? dlsym(library, fallback) : NULL);
}

int64_t simple_audio_cuda_open(void) {
    void *library = dlopen("libcuda.so.1", RTLD_NOW | RTLD_LOCAL);
    if (!library) library = dlopen("libcuda.so", RTLD_NOW | RTLD_LOCAL);
    if (!library) return 0;
    cu_init_fn init = (cu_init_fn)symbol(library, "cuInit", NULL);
    cu_device_count_fn count = (cu_device_count_fn)symbol(library, "cuDeviceGetCount", NULL);
    cu_device_get_fn get = (cu_device_get_fn)symbol(library, "cuDeviceGet", NULL);
    cu_ctx_create_fn create = (cu_ctx_create_fn)symbol(library, "cuCtxCreate_v2", "cuCtxCreate");
    struct simple_audio_cuda *driver = calloc(1, sizeof(*driver));
    if (!driver || !init || !count || !get || !create) goto fail;
    driver->library = library;
    driver->ctx_destroy = (cu_ctx_destroy_fn)symbol(library, "cuCtxDestroy_v2", "cuCtxDestroy");
    driver->module_load = (cu_module_load_fn)symbol(library, "cuModuleLoadData", NULL);
    driver->module_unload = (cu_module_unload_fn)symbol(library, "cuModuleUnload", NULL);
    driver->module_get = (cu_module_get_fn)symbol(library, "cuModuleGetFunction", NULL);
    driver->mem_alloc = (cu_mem_alloc_fn)symbol(library, "cuMemAlloc_v2", "cuMemAlloc");
    driver->mem_free = (cu_mem_free_fn)symbol(library, "cuMemFree_v2", "cuMemFree");
    driver->copy_htod = (cu_copy_htod_fn)symbol(library, "cuMemcpyHtoD_v2", "cuMemcpyHtoD");
    driver->copy_dtoh = (cu_copy_dtoh_fn)symbol(library, "cuMemcpyDtoH_v2", "cuMemcpyDtoH");
    driver->sync = (cu_sync_fn)symbol(library, "cuCtxSynchronize", NULL);
    driver->launch = (cu_launch_fn)symbol(library, "cuLaunchKernel", NULL);
    int devices = 0;
    if (!driver->ctx_destroy || !driver->module_load || !driver->module_unload ||
        !driver->module_get || !driver->mem_alloc || !driver->mem_free ||
        !driver->copy_htod || !driver->copy_dtoh || !driver->sync || !driver->launch ||
        init(0) != 0 || count(&devices) != 0 || devices < 1 ||
        get(&driver->device, 0) != 0 || create(&driver->context, 0, driver->device) != 0)
        goto fail;
    return (int64_t)(uintptr_t)driver;
fail:
    if (driver) free(driver);
    dlclose(library);
    return 0;
}

int64_t simple_audio_cuda_close(int64_t raw) {
    struct simple_audio_cuda *d = (struct simple_audio_cuda *)(uintptr_t)raw;
    if (!d) return 1;
    if (d->context) d->ctx_destroy(d->context);
    dlclose(d->library);
    free(d);
    return 0;
}

int64_t simple_audio_cuda_module_load(int64_t raw, int64_t ptx) {
    struct simple_audio_cuda *d = (struct simple_audio_cuda *)(uintptr_t)raw;
    void *module = NULL;
    return d && ptx && d->module_load(&module, (const void *)(uintptr_t)ptx) == 0
        ? (int64_t)(uintptr_t)module : 0;
}
int64_t simple_audio_cuda_module_unload(int64_t raw, int64_t module) {
    struct simple_audio_cuda *d = (struct simple_audio_cuda *)(uintptr_t)raw;
    return d && module ? d->module_unload((void *)(uintptr_t)module) : 1;
}
int64_t simple_audio_cuda_alloc(int64_t raw, int64_t size) {
    struct simple_audio_cuda *d = (struct simple_audio_cuda *)(uintptr_t)raw;
    uint64_t ptr = 0;
    return d && size > 0 && d->mem_alloc(&ptr, (size_t)size) == 0 ? (int64_t)ptr : 0;
}
int64_t simple_audio_cuda_free(int64_t raw, int64_t ptr) {
    struct simple_audio_cuda *d = (struct simple_audio_cuda *)(uintptr_t)raw;
    return d && ptr ? d->mem_free((uint64_t)ptr) : 1;
}
int64_t simple_audio_cuda_upload(int64_t raw, int64_t dst, int64_t src, int64_t size) {
    struct simple_audio_cuda *d = (struct simple_audio_cuda *)(uintptr_t)raw;
    return d && dst && src && size > 0 ? d->copy_htod((uint64_t)dst, (void *)(uintptr_t)src, (size_t)size) : 1;
}
int64_t simple_audio_cuda_download(int64_t raw, int64_t dst, int64_t src, int64_t size) {
    struct simple_audio_cuda *d = (struct simple_audio_cuda *)(uintptr_t)raw;
    return d && dst && src && size > 0 ? d->copy_dtoh((void *)(uintptr_t)dst, (uint64_t)src, (size_t)size) : 1;
}
int64_t simple_audio_cuda_launch(int64_t raw, int64_t module, int64_t name,
    int64_t grid_x, int64_t block_x, int64_t args) {
    struct simple_audio_cuda *d = (struct simple_audio_cuda *)(uintptr_t)raw;
    void *function = NULL;
    if (!d || !module || !name || !args || grid_x < 1 || block_x < 1 ||
        d->module_get(&function, (void *)(uintptr_t)module, (const char *)(uintptr_t)name) != 0)
        return 1;
    return d->launch(function, (unsigned)grid_x, 1, 1, (unsigned)block_x, 1, 1,
        0, NULL, (void **)(uintptr_t)args, NULL);
}
int64_t simple_audio_cuda_sync(int64_t raw) {
    struct simple_audio_cuda *d = (struct simple_audio_cuda *)(uintptr_t)raw;
    return d ? d->sync() : 1;
}
int64_t simple_audio_cuda_identity(int64_t raw) {
    struct simple_audio_cuda *d = (struct simple_audio_cuda *)(uintptr_t)raw;
    return d ? (int64_t)d->device + 1 : 0;
}
