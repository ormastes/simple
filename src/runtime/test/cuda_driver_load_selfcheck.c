/* CUDA driver loading for the C CUDA provider (bitmap_provider_v1.c):
 *  - fail-closed named errors (CUDA-E001 missing library, CUDA-E002 missing
 *    symbol), matching src/lib/gc_async_mut/cuda/driver_loader.spl;
 *  - the platform candidate list (nvcuda.dll on Windows, libcuda.so.1 /
 *    libcuda.so elsewhere) with a real cuInit + cuDeviceGetCount when a driver
 *    is installed, then a real context create/destroy on device 0.
 * No CUDA driver on the host is exit 77 (UNSUPPORTED), never PASS. */
#include "../providers/cuda/bitmap_provider_v1.c"
#include <stdio.h>
#define CHECK(x) do { if (!(x)) { fprintf(stderr,"FAIL line=%d %s\n",__LINE__,#x); return 1; } } while (0)
/* An always-present, never-CUDA system library per OS (must resolve through
 * the provider's own loader, which is System32-only on Windows). */
#if defined(_WIN32)
#define NOT_CUDA "kernel32.dll"
#elif defined(__APPLE__)
#define NOT_CUDA "/usr/lib/libSystem.B.dylib"
#elif defined(__FreeBSD__)
#define NOT_CUDA "libc.so.7"
#elif defined(__linux__) && defined(__GLIBC__)
#define NOT_CUDA "libc.so.6"
#else
#define NOT_CUDA NULL /* no known always-present library: E002 probe skipped */
#endif

int main(void) {
    char err[512];
    CHECK(load_driver_table("simple_no_such_cuda_driver_lib", err, sizeof(err)) == NULL);
    CHECK(strncmp(err, "CUDA-E001:", 10) == 0);
    CHECK(strstr(err, "simple_no_such_cuda_driver_lib") != NULL);
    const char *not_cuda = NOT_CUDA;
    if (not_cuda != NULL) {
        CHECK(load_driver_table(not_cuda, err, sizeof(err)) == NULL);
        CHECK(strncmp(err, "CUDA-E002:", 10) == 0);
        CHECK(strstr(err, "cuInit") != NULL);
    } else {
        printf("SKIP CUDA-E002 probe: no known non-CUDA system library on this OS\n");
    }

    if (!load_driver()) {
        const char *why = simple_cuda_provider_last_error_v1();
        CHECK(why && strncmp(why, "CUDA-E00", 8) == 0);
        printf("UNSUPPORTED no CUDA driver: %s\n", why);
        return 77;
    }
    CHECK(simple_cuda_provider_last_error_v1()[0] == '\0');
    const struct driver_table *first = published_driver();
    CHECK(first != NULL);
    CHECK(load_driver() && published_driver() == first); /* published once */

    int count = 0;
    CHECK(driver.Init(0) == 0);
    CHECK(driver.DeviceGetCount(&count) == 0);
    CHECK(count > 0);

    int dev = -1; void *ctx = NULL;
    CHECK(driver.DeviceGet(&dev, 0) == 0 && dev >= 0);
    CHECK(driver.CtxCreate(&ctx, 0, dev) == 0 && ctx != NULL);
    /* The embedded PTX must JIT on this device and the kernel must run. */
    CHECK(ptx_header(1, 3) == NULL && ptx_header(2, 1) != NULL && ptx_header(12, 0) != NULL);
    CHECK(load_module(dev) == 0);
    void *fn = NULL;
    CHECK(driver.ModuleGetFunction(&fn, state.module, "bitmap_and") == 0 && fn != NULL);
    enum { N = 300 };
    uint32_t a[N], b[N], o[N];
    for (uint32_t i = 0; i < N; i++) { a[i] = 0xF0F0F0F0u ^ i; b[i] = 0x0FF00FF0u + i * 7u; o[i] = 0; }
    DevPtr da = 0, db = 0, dout = 0;
    CHECK(driver.MemAlloc(&da, sizeof(a)) == 0 && driver.MemAlloc(&db, sizeof(b)) == 0 &&
          driver.MemAlloc(&dout, sizeof(o)) == 0);
    CHECK(driver.MemcpyHtoD(da, a, sizeof(a)) == 0 && driver.MemcpyHtoD(db, b, sizeof(b)) == 0);
    uint32_t n = N;
    void *args[] = {&da, &db, &dout, &n};
    CHECK(driver.LaunchKernel(fn, (N + 127) / 128, 1, 1, 128, 1, 1, 0, NULL, args, NULL) == 0);
    CHECK(driver.CtxSynchronize() == 0);
    CHECK(driver.MemcpyDtoH(o, dout, sizeof(o)) == 0);
    for (uint32_t i = 0; i < N; i++) CHECK(o[i] == (a[i] & b[i]));
    CHECK(driver.MemFree(da) == 0 && driver.MemFree(db) == 0 && driver.MemFree(dout) == 0);
    CHECK(driver.ModuleUnload(state.module) == 0);
    state.module = NULL;
    CHECK(driver.CtxDestroy(ctx) == 0);
    CHECK(shutdown_provider() == OK && published_driver() == NULL);
    printf("cuda_driver_load=pass library=%s devices=%d real_context=ok kernel_launch=ok\n", CUDA_DRIVER_PRIMARY, count);
    return 0;
}
