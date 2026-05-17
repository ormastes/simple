#include <stdint.h>
#include <stddef.h>

uint64_t rt_fnv_hash(const uint8_t *data_ptr, uint64_t data_len) {
    if (data_ptr == NULL) return 0;
    uint64_t hash = 0xcbf29ce484222325ULL;
    const uint64_t prime = 0x00000100000001b3ULL;
    for (uint64_t i = 0; i < data_len; i++) {
        hash ^= (uint64_t)data_ptr[i];
        hash *= prime;
    }
    return hash;
}
