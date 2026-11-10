/* Compiled after the exact malloc/free/realloc/calloc + NVMe allocation owner
 * extracted from baremetal_stubs.c by check-simpleos-reclaim-heap.shs. Only
 * serial diagnostics and the hardware panic exit are adapted for the host. */
int main(void)
{
    unsigned checks = 0;
#define OWNER_CHECK(c) do { ++checks; if (!(c)) { \
    fprintf(stderr, "FAIL owner line %d: %s\n", __LINE__, #c); return 1; \
} } while (0)
    OWNER_CHECK(BAREMETAL_HEAP_SIZE == sizeof(_heap));
    unsigned char *retained = malloc(64);
    memset(retained, 0x5a, 64);
    size_t baseline = _heap_off;
    for (unsigned frame = 0; frame < 100; ++frame) {
        unsigned char *temporary = malloc(1024 * 1024);
        memset(temporary, (unsigned char)frame, 1024 * 1024);
        free(temporary);
        OWNER_CHECK(_heap_off == baseline);
        OWNER_CHECK(retained[0] == 0x5a && retained[63] == 0x5a);
    }
    unsigned char *zeroed = calloc(3, 17);
    for (unsigned i = 0; i < 51; ++i) OWNER_CHECK(zeroed[i] == 0);
    zeroed[0] = 0x31;
    void *barrier = malloc(64);
    unsigned char *grown = simpleos_heap_realloc_last(zeroed, 51, 8192);
    OWNER_CHECK(grown && grown[0] == 0x31);
    free(grown);
    free(barrier);
    OWNER_CHECK(_heap_off == baseline);
    unsigned char *nvme_a = nvme_alloc_aligned(4096, 4096);
    unsigned char *nvme_b = nvme_alloc_aligned(8192, 4096);
    OWNER_CHECK(nvme_a && nvme_b);
    OWNER_CHECK(((uintptr_t)nvme_a & 4095) == 0);
    OWNER_CHECK(((uintptr_t)nvme_b & 4095) == 0);
    memset(nvme_b, 0xc3, 8192);
    nvme_free_aligned(nvme_a); /* Non-LIFO DMA buffer release. */
    OWNER_CHECK(nvme_b[0] == 0xc3 && nvme_b[8191] == 0xc3);
    void *reuse = malloc(2048);
    OWNER_CHECK(reuse != NULL);
    nvme_free_aligned(nvme_b);
    free(reuse);
    OWNER_CHECK(_heap_off == baseline);
    OWNER_CHECK(nvme_alloc_aligned(64, 3) == NULL);
    OWNER_CHECK(nvme_alloc_aligned(SIZE_MAX, 4096) == NULL);
    free(retained);
    OWNER_CHECK(_heap_off == 0);
    printf("PASS simpleos allocation owner: %u assertions; retained + frame scratch + NVMe\n", checks);
    return 0;
}
