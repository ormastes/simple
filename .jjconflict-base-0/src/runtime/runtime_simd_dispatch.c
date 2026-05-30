/*
 * SIMD Dispatch — compilation unit for dispatch table support.
 * The text dispatch table (g_simd_text) and init are in runtime_simd_utf8.c.
 * The crypto dispatch table (g_simd_crypto) is defined here with scalar stubs.
 */
#include "runtime_simd_dispatch.h"

/* Scalar fallback stubs — no-op placeholders until pure Simple or
   hardware-accelerated implementations are wired in. */

static void scalar_aes_encrypt_block(const uint8_t* in, uint8_t* out,
                                     const uint8_t* round_keys, int rounds) {
    (void)in; (void)out; (void)round_keys; (void)rounds;
}

static void scalar_aes_decrypt_block(const uint8_t* in, uint8_t* out,
                                     const uint8_t* round_keys, int rounds) {
    (void)in; (void)out; (void)round_keys; (void)rounds;
}

static void scalar_sha256_compress(uint32_t state[8], const uint8_t* block) {
    (void)state; (void)block;
}

static void scalar_chacha20_block(uint32_t out[16], const uint32_t in[16]) {
    (void)out; (void)in;
}

static uint32_t scalar_crc32_update(uint32_t crc, const uint8_t* data, uint64_t len) {
    (void)data; (void)len;
    return crc;
}

static void scalar_ghash_multiply(uint8_t* result, const uint8_t* h, const uint8_t* x) {
    (void)result; (void)h; (void)x;
}

SimdCryptoDispatch g_simd_crypto = {
    .aes_encrypt_block = scalar_aes_encrypt_block,
    .aes_decrypt_block = scalar_aes_decrypt_block,
    .sha256_compress   = scalar_sha256_compress,
    .chacha20_block    = scalar_chacha20_block,
    .crc32_update      = scalar_crc32_update,
    .ghash_multiply    = scalar_ghash_multiply,
};

void simd_crypto_init(void) {
    /* Detect hardware crypto extensions and upgrade function pointers.
       AES-NI, SHA-NI, and PCLMULQDQ implementations will be added as
       separate TUs (runtime_simd_aesni.c, runtime_simd_shani.c, etc.)
       and wired in here when available. */
}
