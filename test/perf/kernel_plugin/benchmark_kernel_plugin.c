#define _POSIX_C_SOURCE 200809L
#include <dlfcn.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef uint64_t (*kpf_batch_fn)(const uint8_t *, size_t, uint64_t);
typedef struct { uint32_t abi_version, struct_size; uint64_t schema_digest; kpf_batch_fn invoke_batch; } kpf_benchmark_table;
typedef const kpf_benchmark_table *(*kpf_entry_fn)(void);
typedef struct { uint32_t epoch, pins, cancelled, reserved; } kpf_slot;

static volatile uint64_t sink;
static uint64_t now_ns(void) { struct timespec value; clock_gettime(CLOCK_MONOTONIC, &value); return (uint64_t)value.tv_sec * UINT64_C(1000000000) + (uint64_t)value.tv_nsec; }
static uint64_t direct_batch(const uint8_t *data, size_t size, uint64_t seed) {
    uint64_t value = seed ^ UINT64_C(1469598103934665603);
    for (size_t index = 0; index < size; ++index) { value ^= data[index]; value *= UINT64_C(1099511628211); }
    return value;
}
static uint64_t elapsed_batches(kpf_batch_fn operation, const uint8_t *data, size_t size, size_t rounds) {
    uint64_t value = 1, start = now_ns();
    for (size_t round = 0; round < rounds; ++round) value = operation(data, size, value);
    sink = value;
    return now_ns() - start;
}
static uint64_t slot_work(size_t capacity, size_t rounds) {
    kpf_slot *slots = calloc(capacity, sizeof(*slots));
    if (!slots) return 0;
    uint64_t start = now_ns();
    for (size_t round = 0; round < rounds; ++round) {
        size_t slot = (round * 2654435761u) & (capacity - 1);
        slots[slot].pins += 1; slots[slot].cancelled = 1; slots[slot].pins -= 1; sink += slots[slot].epoch;
    }
    uint64_t elapsed = now_ns() - start;
    free(slots);
    return elapsed;
}
static void sort_u64(uint64_t *values, size_t count) {
    for (size_t outer = 1; outer < count; ++outer) { uint64_t value = values[outer]; size_t inner = outer; while (inner && values[inner - 1] > value) { values[inner] = values[inner - 1]; --inner; } values[inner] = value; }
}
int main(int argc, char **argv) {
    enum { SAMPLES = 21, BATCH_BYTES = 16384, ROUNDS = 2048, SLOT_ROUNDS = 4000000 };
    if (argc != 2) return 2;
    uint8_t *data = malloc(BATCH_BYTES); if (!data) return 3;
    for (size_t index = 0; index < BATCH_BYTES; ++index) data[index] = (uint8_t)(index * 17u + 3u);
    uint64_t admission[SAMPLES]; const kpf_benchmark_table *table = NULL; void *handle = NULL;
    for (size_t sample = 0; sample < SAMPLES; ++sample) {
        uint64_t start = now_ns(); handle = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL); if (!handle) return 4;
        kpf_entry_fn entry = (kpf_entry_fn)dlsym(handle, "simple_kpf_benchmark_provider_v1");
        if (!entry || !(table = entry()) || table->abi_version != 1 || table->struct_size != sizeof(*table) || table->schema_digest != UINT64_C(0x4b504642454e4348) || !table->invoke_batch) return 5;
        admission[sample] = now_ns() - start; if (sample + 1 < SAMPLES) { dlclose(handle); handle = NULL; }
    }
    uint64_t direct[SAMPLES], static_table[SAMPLES], native_table[SAMPLES]; kpf_batch_fn static_slot = direct_batch;
    for (size_t sample = 0; sample < SAMPLES; ++sample) {
        direct[sample] = elapsed_batches(direct_batch, data, BATCH_BYTES, ROUNDS);
        static_table[sample] = elapsed_batches(static_slot, data, BATCH_BYTES, ROUNDS);
        native_table[sample] = elapsed_batches(table->invoke_batch, data, BATCH_BYTES, ROUNDS);
    }
    sort_u64(admission, SAMPLES); sort_u64(direct, SAMPLES); sort_u64(static_table, SAMPLES); sort_u64(native_table, SAMPLES);
    uint64_t small = slot_work(64, SLOT_ROUNDS), large = slot_work(65536, SLOT_ROUNDS);
    printf("samples=%d\nbatch_bytes=%d\nrounds_per_sample=%d\n", SAMPLES, BATCH_BYTES, ROUNDS);
    printf("cold_admission_p50_ns=%" PRIu64 "\ncold_admission_p95_ns=%" PRIu64 "\n", admission[SAMPLES/2], admission[19]);
    printf("direct_p50_ns=%" PRIu64 "\nstatic_table_p50_ns=%" PRIu64 "\nnative_table_p50_ns=%" PRIu64 "\n", direct[SAMPLES/2], static_table[SAMPLES/2], native_table[SAMPLES/2]);
    printf("static_overhead_ppm=%" PRIu64 "\nnative_overhead_ppm=%" PRIu64 "\n", static_table[SAMPLES/2] * UINT64_C(1000000) / direct[SAMPLES/2] - UINT64_C(1000000), native_table[SAMPLES/2] * UINT64_C(1000000) / direct[SAMPLES/2] - UINT64_C(1000000));
    printf("slot_small_ns=%" PRIu64 "\nslot_large_ns=%" PRIu64 "\nslot_scaling_ppm=%" PRIu64 "\n", small, large, large * UINT64_C(1000000) / small);
    printf("slot_bytes=%zu\nfixed_queue_bytes_1024=%zu\n", sizeof(kpf_slot), sizeof(kpf_slot) * 1024u);
    dlclose(handle); free(data); return 0;
}
