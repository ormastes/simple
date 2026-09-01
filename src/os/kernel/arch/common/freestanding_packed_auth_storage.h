#ifndef SIMPLEOS_FREESTANDING_PACKED_AUTH_STORAGE_H
#define SIMPLEOS_FREESTANDING_PACKED_AUTH_STORAGE_H

#include <stdint.h>

#define SIMPLEOS_PACKED_AUTH_STORAGE_SLOTS 16U
#define SIMPLEOS_PACKED_AUTH_SECRET_BYTES 16U
#define SIMPLEOS_PACKED_AUTH_MESSAGE_BYTES 80U
#define SIMPLEOS_PACKED_AUTH_X86_TOKEN_BYTES 96U

typedef enum {
    SIMPLEOS_PACKED_AUTH_SECRET = 1,
    SIMPLEOS_PACKED_AUTH_MESSAGE = 2,
    SIMPLEOS_PACKED_AUTH_X86_TOKEN = 3
} SimpleOsPackedAuthKind;

typedef struct {
    uint32_t kind;
    uint32_t slot;
    uint32_t generation;
} SimpleOsPackedAuthLease;

/* Claims one stable kernel-only record. A zero generation is always invalid. */
int32_t simpleos_packed_auth_claim(uint32_t kind,
                                   SimpleOsPackedAuthLease *lease_out);

/* Copies exactly the record size, one byte at a time, into owned storage. */
int32_t simpleos_packed_auth_write(SimpleOsPackedAuthLease lease,
                                   const uint8_t *source,
                                   uint32_t source_len);

/* Copies exactly the record size out without transferring ownership. */
int32_t simpleos_packed_auth_read(SimpleOsPackedAuthLease lease,
                                  uint8_t *destination,
                                  uint32_t destination_len);

/* Stable only while the exact lease remains live; never publish to user/DMA. */
uintptr_t simpleos_packed_auth_address(SimpleOsPackedAuthLease lease);

/* Exact-lease release wipes every byte before making the slot reusable. */
int32_t simpleos_packed_auth_release(SimpleOsPackedAuthLease lease);

/* Scalar Simple/ILP32 bridge: packed lease is kind:8 | slot:8 | generation:32. */
uint64_t rt_packed_auth_claim(uint32_t kind);
int32_t rt_packed_auth_write_byte(uint64_t packed_lease,
                                  uint32_t index,
                                  uint32_t value);
uint64_t rt_packed_auth_address(uint64_t packed_lease);
int32_t rt_packed_auth_release(uint64_t packed_lease);

#endif
