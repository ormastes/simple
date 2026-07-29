#include <stdint.h>

static uint8_t buffers[4][16384] __attribute__((aligned(4096)));
static int live[4];
static int64_t calls;
static int64_t fail_at;

void rt_hda_dma_probe_reset(int64_t fail_call) {
    for (int i = 0; i < 4; ++i) live[i] = 0;
    calls = 0;
    fail_at = fail_call;
}

int64_t rt_hda_dma_probe_live_count(void) {
    int64_t count = 0;
    for (int i = 0; i < 4; ++i) count += live[i];
    return count;
}

int64_t rt_dma_alloc(int64_t size, int32_t dir_raw) {
    (void)size;
    (void)dir_raw;
    ++calls;
    if (calls == fail_at || calls > 4) return -1;
    live[calls - 1] = 1;
    return calls - 1;
}

void rt_dma_free(int64_t handle) {
    if (handle >= 0 && handle < 4) live[handle] = 0;
}

int64_t rt_dma_virt_of(int64_t handle) {
    if (handle < 0 || handle >= 4 || !live[handle]) return 0;
    return (int64_t)(uintptr_t)buffers[handle];
}

int64_t rt_dma_phys_of(int64_t handle) {
    return rt_dma_virt_of(handle);
}
