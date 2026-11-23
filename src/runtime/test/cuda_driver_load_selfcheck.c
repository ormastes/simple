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
#ifdef _WIN32
#define NOT_CUDA "kernel32.dll"
#else
#define NOT_CUDA "libc.so.6"
#endif

int main(void) {
    char err[512];
    CHECK(load_driver_table("simple_no_such_cuda_driver_lib", err, sizeof(err)) == NULL);
    CHECK(strncmp(err, "CUDA-E001:", 10) == 0);
    CHECK(strstr(err, "simple_no_such_cuda_driver_lib") != NULL);
    CHECK(load_driver_table(NOT_CUDA, err, sizeof(err)) == NULL);
    CHECK(strncmp(err, "CUDA-E002:", 10) == 0);
    CHECK(strstr(err, "cuInit") != NULL);

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
    CHECK(driver.CtxDestroy(ctx) == 0);
    CHECK(shutdown_provider() == OK && published_driver() == NULL);
    printf("cuda_driver_load=pass library=%s devices=%d real_context=ok\n", CUDA_DRIVER_PRIMARY, count);
    return 0;
}
