#define _GNU_SOURCE
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <sched.h>
#include <time.h>

extern bool rt_simd_has_sse(void);
extern bool rt_simd_has_avx(void);
extern bool rt_simd_has_avx2(void);
static pthread_barrier_t start;
static unsigned results[8];
static unsigned features(void) {
    return rt_simd_has_sse() | (rt_simd_has_avx() << 1) | (rt_simd_has_avx2() << 2);
}
static void *first_queries(void *arg) {
    const unsigned slot = (unsigned)(uintptr_t)arg;
    pthread_barrier_wait(&start);
    unsigned first = features();
    for (unsigned i = 0; i < 256; ++i)
        if (features() != first) return (void *)1;
    results[slot] = first;
    return NULL;
}
static uint64_t now_ns(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts)) abort();
    return (uint64_t)ts.tv_sec * UINT64_C(1000000000) + ts.tv_nsec;
}
int main(int argc, char **argv) {
    if (argc != 2) return 2;
    const int cpu = atoi(argv[1]);
    pthread_t threads[8];
    if (pthread_barrier_init(&start, NULL, 8)) return 3;
    for (unsigned i = 0; i < 8; ++i)
        if (pthread_create(&threads[i], NULL, first_queries, (void *)(uintptr_t)i)) return 4;
    for (unsigned i = 0; i < 8; ++i) {
        void *result;
        if (pthread_join(threads[i], &result) || result || results[i] != results[0]) return 5;
    }
    pthread_barrier_destroy(&start);
    cpu_set_t set;
    CPU_ZERO(&set);
    if (cpu < 0 || cpu >= CPU_SETSIZE) return 6;
    CPU_SET(cpu, &set);
    if (sched_setaffinity(0, sizeof(set), &set)) return 7;
    printf("features=%u first_use_threads=8 cpu=%d iterations=200000\n", results[0], cpu);
    for (unsigned sample = 0; sample < 7; ++sample) {
        uint64_t checksum = 0, begin = now_ns();
        for (unsigned i = 0; i < 200000; ++i) checksum += features();
        uint64_t elapsed = now_ns() - begin;
        if (checksum != UINT64_C(200000) * results[0]) return 8;
        printf("sample=%u ns_per_query=%.3f checksum=%llu\n", sample,
               (double)elapsed / 600000.0, (unsigned long long)checksum);
    }
    return 0;
}
