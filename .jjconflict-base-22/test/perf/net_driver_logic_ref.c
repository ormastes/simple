#include <stdint.h>
#include <stdio.h>
#include <time.h>

static inline int64_t now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000000000LL + (int64_t)ts.tv_nsec;
}

static inline uint64_t nd_desc_size(uint64_t queue_size) { return queue_size * 16; }
static inline uint64_t nd_avail_size(uint64_t queue_size) { return 4 + queue_size * 2; }
static inline uint64_t nd_used_size(uint64_t queue_size) { return 4 + queue_size * 8; }
static inline uint64_t nd_total_size(uint64_t queue_size) {
    uint64_t desc_avail = nd_desc_size(queue_size) + nd_avail_size(queue_size);
    return ((desc_avail + 4095) & ~4095ULL) + nd_used_size(queue_size);
}

static void print_row(const char *label, int64_t iters, int64_t total_ns, uint64_t checksum) {
    printf("%s,%lld,%lld,%llu\n", label, (long long)iters, (long long)total_ns, (unsigned long long)checksum);
}

#define RUN_CASE(label, body) \
    do { \
        uint64_t checksum = 0; \
        int64_t t0 = now_ns(); \
        for (int64_t i = 0; i < iters; i++) { body; } \
        print_row(label, iters, now_ns() - t0, checksum); \
    } while (0)

int main(void) {
    const int64_t iters = 200000;
    puts("label,iters,total_ns,checksum");
    RUN_CASE("desc", checksum += nd_desc_size((uint64_t)((i % 128) + 1)));
    RUN_CASE("avail", checksum += nd_avail_size((uint64_t)((i % 128) + 1)));
    RUN_CASE("used", checksum += nd_used_size((uint64_t)((i % 128) + 1)));
    RUN_CASE("total", checksum += nd_total_size((uint64_t)((i % 128) + 1)));
    RUN_CASE("ring", checksum += 0x1000ULL + 4 + (((uint64_t)i % 128) * 2));
    RUN_CASE("used_align", {
        uint64_t q = (uint64_t)((i % 128) + 1);
        uint64_t desc_avail = nd_desc_size(q) + nd_avail_size(q);
        checksum += ((desc_avail + 4095) & ~4095ULL);
    });
    RUN_CASE("pfn", checksum += ((0x80000000ULL + (uint64_t)i * 4096) >> 12));
    RUN_CASE("descriptor", checksum += 0x100000ULL + (((uint64_t)i % 128) * 16));
    RUN_CASE("buffer", checksum += 0x200000ULL + (((uint64_t)i % 128) * 2048) + 10);
    RUN_CASE("tx_pair", {
        uint64_t head = (uint64_t)i % 128;
        uint64_t payload = (head + 1) % 128;
        checksum += (head * 16) + (payload * 16);
    });
    RUN_CASE("phys_split", {
        uint64_t phys = 0x100000000ULL + (uint64_t)i * 2048;
        checksum += (phys & 0xFFFFFFFFULL) + (phys >> 32);
    });
    return 0;
}
