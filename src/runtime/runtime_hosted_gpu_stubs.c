#include <stdint.h>

/* Optional GPU transports that have no native hosted provider on this host.
 * Keep their ABI owned and fail closed so importing a multi-backend Engine2D
 * facade does not leave otherwise-unselected backends as unresolved symbols.
 */
int64_t rt_engine2d_rocm_download_pixels(int64_t src, int64_t pixels, int64_t byte_size) {
    (void)src;
    (void)pixels;
    (void)byte_size;
    return -3;
}

int64_t rt_engine2d_rocm_upload_host_buf(int64_t dst, int64_t host_buf, int64_t byte_size) {
    (void)dst;
    (void)host_buf;
    (void)byte_size;
    return -3;
}
