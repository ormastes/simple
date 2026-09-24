#include <stddef.h>
#include <stdint.h>

typedef uint64_t (*kpf_batch_fn)(const uint8_t *, size_t, uint64_t);

typedef struct {
    uint32_t abi_version;
    uint32_t struct_size;
    uint64_t schema_digest;
    kpf_batch_fn invoke_batch;
} kpf_benchmark_table;

static uint64_t provider_batch(const uint8_t *data, size_t size, uint64_t seed) {
    uint64_t value = seed ^ UINT64_C(1469598103934665603);
    for (size_t index = 0; index < size; ++index) {
        value ^= data[index];
        value *= UINT64_C(1099511628211);
    }
    return value;
}

const kpf_benchmark_table *simple_kpf_benchmark_provider_v1(void) {
    static const kpf_benchmark_table table = {
        1, sizeof(kpf_benchmark_table), UINT64_C(0x4b504642454e4348), provider_batch
    };
    return &table;
}
