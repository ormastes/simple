#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>

#define DATA_SIZE 65536ULL
#define TRAVERSE_ITERS 1800ULL
#define PUSH_SIZE 32768ULL
#define PUSH_ITERS 120ULL
#define SET_SIZE 1024ULL
#define SET_ITERS 200ULL

static uint64_t now_us(void) {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return (uint64_t)tv.tv_sec * 1000000ULL + (uint64_t)tv.tv_usec;
}

static void report(const char *bench, uint64_t ops, uint64_t micros, uint64_t checksum) {
    if (micros == 0) micros = 1;
    printf("[collectionbench] lang=c bench=%s ops=%llu micros=%llu ops_per_ms=%llu checksum=%llu\n",
           bench, (unsigned long long)ops, (unsigned long long)micros,
           (unsigned long long)((ops * 1000ULL) / micros), (unsigned long long)checksum);
}

static uint64_t *make_data(void) {
    uint64_t *data = (uint64_t *)malloc(sizeof(uint64_t) * DATA_SIZE);
    for (uint64_t i = 0; i < DATA_SIZE; i++) data[i] = (i * 131ULL + 17ULL) & 0xffffULL;
    return data;
}

static void bench_list_traverse(uint64_t *data) {
    uint64_t checksum = 0;
    uint64_t start = now_us();
    for (uint64_t iter = 0; iter < TRAVERSE_ITERS; iter++) {
        for (uint64_t i = 0; i < DATA_SIZE; i++) checksum += data[i] ^ iter;
    }
    report("list_traverse", DATA_SIZE * TRAVERSE_ITERS, now_us() - start, checksum);
}

static void bench_list_push(void) {
    uint64_t checksum = 0;
    uint64_t start = now_us();
    for (uint64_t iter = 0; iter < PUSH_ITERS; iter++) {
        uint64_t *data = (uint64_t *)malloc(sizeof(uint64_t) * PUSH_SIZE);
        for (uint64_t i = 0; i < PUSH_SIZE; i++) {
            data[i] = i ^ iter;
            checksum += data[i];
        }
        free(data);
    }
    report("list_push", PUSH_SIZE * PUSH_ITERS, now_us() - start, checksum);
}

static void bench_set_contains(void) {
    uint64_t keys[SET_SIZE];
    for (uint64_t i = 0; i < SET_SIZE; i++) {
        keys[i] = (i * 131ULL + 7ULL) | 1ULL;
    }

    uint64_t checksum = 0;
    uint64_t start = now_us();
    for (uint64_t iter = 0; iter < SET_ITERS; iter++) {
        for (uint64_t i = 0; i < SET_SIZE; i++) {
            uint64_t key = (i * 131ULL + 7ULL) | 1ULL;
            for (uint64_t slot = 0; slot < SET_SIZE; slot++) {
                if (keys[slot] == key) {
                    checksum += key ^ iter;
                    break;
                }
            }
        }
    }
    report("set_contains", SET_SIZE * SET_ITERS, now_us() - start, checksum);
}

int main(void) {
    uint64_t *data = make_data();
    bench_list_traverse(data);
    bench_list_push();
    bench_set_contains();
    free(data);
    return 0;
}
