#ifndef SIMPLE_SQLITE_PROVIDER_ABI_V1_H
#define SIMPLE_SQLITE_PROVIDER_ABI_V1_H

#include <stdint.h>

#define SIMPLE_SQLITE_PROVIDER_ABI_V1 1

/* The host supplies the Simple string ABI, so the provider has no undefined
 * references to executable runtime symbols when loaded by dlopen. */
typedef struct SimpleSqliteRuntimeApiV1 {
    uint64_t struct_size;
    uint64_t abi_version;
    int64_t (*string_new)(const uint8_t *, uint64_t);
    const uint8_t *(*string_data)(int64_t);
    int64_t (*string_len)(int64_t);
} SimpleSqliteRuntimeApiV1;

#endif
