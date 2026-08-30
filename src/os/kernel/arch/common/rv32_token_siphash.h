#ifndef SIMPLEOS_RV32_TOKEN_SIPHASH_H
#define SIMPLEOS_RV32_TOKEN_SIPHASH_H

#include <stdint.h>

uint64_t rt_rv32_token_siphash24(uint32_t key_address,
                                 uint32_t message_address,
                                 uint32_t message_len);

/* Host/static KAT entry avoids truncating native pointers through the RV32 ABI. */
uint64_t simpleos_token_siphash24_bytes(const uint8_t key[16],
                                        const uint8_t *message,
                                        uint32_t message_len);

#endif
