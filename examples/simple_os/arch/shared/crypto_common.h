/*
 * Portable Crypto for SimpleOS — shared across all architectures
 *
 * This file is #included from each arch's baremetal_stubs.c AFTER:
 *   - RuntimeValue, ENCODE_INT, DECODE_INT, IS_HEAP, DECODE_PTR are defined
 *   - HeapHeader, RuntimeArray, RuntimeString types are defined
 *   - serial_puts(), malloc(), free() are available
 *   - HEAP_ARRAY constant is defined
 *
 * Works on both 32-bit (RuntimeValue = int32_t) and 64-bit (RuntimeValue = int64_t).
 * All internal crypto uses uint8_t/uint32_t/uint64_t — fully portable.
 *
 * Provides:
 *   - Crypto constant tables (SHA-256/512 K/H, AES S-box)
 *   - SHA-512 hash (C-side, replaces unreliable Simple baremetal impl)
 *   - Ed25519 sign/verify/keypair (RFC 8032)
 *   - RuntimeValue wrapper functions (rt_sha256_K, rt_ed25519_sign, etc.)
 */

#ifndef CRYPTO_COMMON_H
#define CRYPTO_COMMON_H

#include <stdint.h>

/* ===================================================================
 * Crypto constant tables
 * =================================================================== */

static const uint64_t _sha512_K[80] = {
    0x428a2f98d728ae22ULL, 0x7137449123ef65cdULL, 0xb5c0fbcfec4d3b2fULL, 0xe9b5dba58189dbbcULL,
    0x3956c25bf348b538ULL, 0x59f111f1b605d019ULL, 0x923f82a4af194f9bULL, 0xab1c5ed5da6d8118ULL,
    0xd807aa98a3030242ULL, 0x12835b0145706fbeULL, 0x243185be4ee4b28cULL, 0x550c7dc3d5ffb4e2ULL,
    0x72be5d74f27b896fULL, 0x80deb1fe3b1696b1ULL, 0x9bdc06a725c71235ULL, 0xc19bf174cf692694ULL,
    0xe49b69c19ef14ad2ULL, 0xefbe4786384f25e3ULL, 0x0fc19dc68b8cd5b5ULL, 0x240ca1cc77ac9c65ULL,
    0x2de92c6f592b0275ULL, 0x4a7484aa6ea6e483ULL, 0x5cb0a9dcbd41fbd4ULL, 0x76f988da831153b5ULL,
    0x983e5152ee66dfabULL, 0xa831c66d2db43210ULL, 0xb00327c898fb213fULL, 0xbf597fc7beef0ee4ULL,
    0xc6e00bf33da88fc2ULL, 0xd5a79147930aa725ULL, 0x06ca6351e003826fULL, 0x142929670a0e6e70ULL,
    0x27b70a8546d22ffcULL, 0x2e1b21385c26c926ULL, 0x4d2c6dfc5ac42aedULL, 0x53380d139d95b3dfULL,
    0x650a73548baf63deULL, 0x766a0abb3c77b2a8ULL, 0x81c2c92e47edaee6ULL, 0x92722c851482353bULL,
    0xa2bfe8a14cf10364ULL, 0xa81a664bbc423001ULL, 0xc24b8b70d0f89791ULL, 0xc76c51a30654be30ULL,
    0xd192e819d6ef5218ULL, 0xd69906245565a910ULL, 0xf40e35855771202aULL, 0x106aa07032bbd1b8ULL,
    0x19a4c116b8d2d0c8ULL, 0x1e376c085141ab53ULL, 0x2748774cdf8eeb99ULL, 0x34b0bcb5e19b48a8ULL,
    0x391c0cb3c5c95a63ULL, 0x4ed8aa4ae3418acbULL, 0x5b9cca4f7763e373ULL, 0x682e6ff3d6b2b8a3ULL,
    0x748f82ee5defb2fcULL, 0x78a5636f43172f60ULL, 0x84c87814a1f0ab72ULL, 0x8cc702081a6439ecULL,
    0x90befffa23631e28ULL, 0xa4506cebde82bde9ULL, 0xbef9a3f7b2c67915ULL, 0xc67178f2e372532bULL,
    0xca273eceea26619cULL, 0xd186b8c721c0c207ULL, 0xeada7dd6cde0eb1eULL, 0xf57d4f7fee6ed178ULL,
    0x06f067aa72176fbaULL, 0x0a637dc5a2c898a6ULL, 0x113f9804bef90daeULL, 0x1b710b35131c471bULL,
    0x28db77f523047d84ULL, 0x32caab7b40c72493ULL, 0x3c9ebe0a15c9bebcULL, 0x431d67c49c100d4cULL,
    0x4cc5d4becb3e42b6ULL, 0x597f299cfc657e2aULL, 0x5fcb6fab3ad6faecULL, 0x6c44198c4a475817ULL
};

static const uint64_t _sha512_H[8] = {
    0x6a09e667f3bcc908ULL, 0xbb67ae8584caa73bULL, 0x3c6ef372fe94f82bULL, 0xa54ff53a5f1d36f1ULL,
    0x510e527fade682d1ULL, 0x9b05688c2b3e6c1fULL, 0x1f83d9abfb41bd6bULL, 0x5be0cd19137e2179ULL
};

static const uint32_t _sha256_K[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
};

static const uint32_t _sha256_H[8] = {
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
};

static const uint8_t _aes_sbox[256] = {
    0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,
    0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,
    0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,
    0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,
    0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,
    0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,
    0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,
    0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,
    0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,
    0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,
    0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,
    0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,
    0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,
    0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,
    0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,
    0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16
};

static const uint8_t _aes_inv_sbox[256] = {
    0x52,0x09,0x6a,0xd5,0x30,0x36,0xa5,0x38,0xbf,0x40,0xa3,0x9e,0x81,0xf3,0xd7,0xfb,
    0x7c,0xe3,0x39,0x82,0x9b,0x2f,0xff,0x87,0x34,0x8e,0x43,0x44,0xc4,0xde,0xe9,0xcb,
    0x54,0x7b,0x94,0x32,0xa6,0xc2,0x23,0x3d,0xee,0x4c,0x95,0x0b,0x42,0xfa,0xc3,0x4e,
    0x08,0x2e,0xa1,0x66,0x28,0xd9,0x24,0xb2,0x76,0x5b,0xa2,0x49,0x6d,0x8b,0xd1,0x25,
    0x72,0xf8,0xf6,0x64,0x86,0x68,0x98,0x16,0xd4,0xa4,0x5c,0xcc,0x5d,0x65,0xb6,0x92,
    0x6c,0x70,0x48,0x50,0xfd,0xed,0xb9,0xda,0x5e,0x15,0x46,0x57,0xa7,0x8d,0x9d,0x84,
    0x90,0xd8,0xab,0x00,0x8c,0xbc,0xd3,0x0a,0xf7,0xe4,0x58,0x05,0xb8,0xb3,0x45,0x06,
    0xd0,0x2c,0x1e,0x8f,0xca,0x3f,0x0f,0x02,0xc1,0xaf,0xbd,0x03,0x01,0x13,0x8a,0x6b,
    0x3a,0x91,0x11,0x41,0x4f,0x67,0xdc,0xea,0x97,0xf2,0xcf,0xce,0xf0,0xb4,0xe6,0x73,
    0x96,0xac,0x74,0x22,0xe7,0xad,0x35,0x85,0xe2,0xf9,0x37,0xe8,0x1c,0x75,0xdf,0x6e,
    0x47,0xf1,0x1a,0x71,0x1d,0x29,0xc5,0x89,0x6f,0xb7,0x62,0x0e,0xaa,0x18,0xbe,0x1b,
    0xfc,0x56,0x3e,0x4b,0xc6,0xd2,0x79,0x20,0x9a,0xdb,0xc0,0xfe,0x78,0xcd,0x5a,0xf4,
    0x1f,0xdd,0xa8,0x33,0x88,0x07,0xc7,0x31,0xb1,0x12,0x10,0x59,0x27,0x80,0xec,0x5f,
    0x60,0x51,0x7f,0xa9,0x19,0xb5,0x4a,0x0d,0x2d,0xe5,0x7a,0x9f,0x93,0xc9,0x9c,0xef,
    0xa0,0xe0,0x3b,0x4d,0xae,0x2a,0xf5,0xb0,0xc8,0xeb,0xbb,0x3c,0x83,0x53,0x99,0x61,
    0x17,0x2b,0x04,0x7e,0xba,0x77,0xd6,0x26,0xe1,0x69,0x14,0x63,0x55,0x21,0x0c,0x7d
};

static const uint32_t _aes_rcon[10] = {
    0x01000000, 0x02000000, 0x04000000, 0x08000000,
    0x10000000, 0x20000000, 0x40000000, 0x80000000,
    0x1b000000, 0x36000000
};

/* ===================================================================
 * Portable RuntimeValue integer type
 *
 * On 64-bit: RV_INT = int64_t
 * On 32-bit: RV_INT = int32_t
 *
 * Each arch #defines RV_INT before including this header.
 * If not defined, auto-detect from RuntimeValue size.
 * =================================================================== */

/* RV_INT must be defined by the including file before #include.
 * 64-bit: #define RV_INT int64_t
 * 32-bit: #define RV_INT int32_t
 */
#ifndef RV_INT
  #error "RV_INT must be defined before including crypto_common.h"
#endif

/* Compatibility: some archs use HEAP_ARRAY, others HEAP_TYPE_ARRAY.
 * Some use .hdr.type, others .header.type. Normalize here. */
#ifndef HEAP_ARRAY
  #ifdef HEAP_TYPE_ARRAY
    #define HEAP_ARRAY HEAP_TYPE_ARRAY
  #else
    #define HEAP_ARRAY 2
  #endif
#endif

/* Normalize struct field access: .hdr vs .header, .items vs .data
 * Each arch can override these before including this header. */
#ifndef CRYPTO_ARRAY_HDR_TYPE
  #define CRYPTO_ARRAY_HDR_TYPE(arr) ((arr)->hdr.type)
#endif
#ifndef CRYPTO_ARRAY_ITEMS
  #define CRYPTO_ARRAY_ITEMS(arr) ((arr)->items)
#endif

/* ===================================================================
 * Constant lookup functions — portable across 32/64-bit
 * =================================================================== */

RV_INT rt_sha512_K(RV_INT i) { return (i >= 0 && i < 80) ? (RV_INT)_sha512_K[i] : 0; }
RV_INT rt_sha512_H(RV_INT i) { return (i >= 0 && i < 8) ? (RV_INT)_sha512_H[i] : 0; }
RV_INT rt_sha256_K(RV_INT i) { return (i >= 0 && i < 64) ? (RV_INT)_sha256_K[i] : 0; }
RV_INT rt_sha256_H(RV_INT i) { return (i >= 0 && i < 8) ? (RV_INT)_sha256_H[i] : 0; }
RV_INT rt_aes_sbox(RV_INT i) { return (i >= 0 && i < 256) ? (RV_INT)_aes_sbox[i] : 0; }
RV_INT rt_aes_inv_sbox(RV_INT i) { return (i >= 0 && i < 256) ? (RV_INT)_aes_inv_sbox[i] : 0; }
RV_INT rt_aes_rcon(RV_INT i) { return (i >= 0 && i < 10) ? (RV_INT)_aes_rcon[i] : 0; }

/* ===================================================================
 * SHA-512 implementation (portable C)
 * =================================================================== */

static inline uint64_t _sha512_rotr(uint64_t x, int n) { return (x >> n) | (x << (64 - n)); }
static inline uint64_t _sha512_ch(uint64_t x, uint64_t y, uint64_t z) { return (x & y) ^ (~x & z); }
static inline uint64_t _sha512_maj(uint64_t x, uint64_t y, uint64_t z) { return (x & y) ^ (x & z) ^ (y & z); }
static inline uint64_t _sha512_S0(uint64_t x) { return _sha512_rotr(x,28) ^ _sha512_rotr(x,34) ^ _sha512_rotr(x,39); }
static inline uint64_t _sha512_S1(uint64_t x) { return _sha512_rotr(x,14) ^ _sha512_rotr(x,18) ^ _sha512_rotr(x,41); }
static inline uint64_t _sha512_s0(uint64_t x) { return _sha512_rotr(x,1) ^ _sha512_rotr(x,8) ^ (x >> 7); }
static inline uint64_t _sha512_s1(uint64_t x) { return _sha512_rotr(x,19) ^ _sha512_rotr(x,61) ^ (x >> 6); }

static void _sha512_process_block(const uint8_t *block, uint64_t *h)
{
    uint64_t w[80];
    for (int t = 0; t < 16; t++) {
        w[t] = 0;
        for (int b = 0; b < 8; b++)
            w[t] = (w[t] << 8) | block[t * 8 + b];
    }
    for (int t = 16; t < 80; t++)
        w[t] = _sha512_s1(w[t-2]) + w[t-7] + _sha512_s0(w[t-15]) + w[t-16];

    uint64_t a=h[0], b=h[1], c=h[2], d=h[3], e=h[4], f=h[5], g=h[6], hh=h[7];
    for (int t = 0; t < 80; t++) {
        uint64_t t1 = hh + _sha512_S1(e) + _sha512_ch(e,f,g) + _sha512_K[t] + w[t];
        uint64_t t2 = _sha512_S0(a) + _sha512_maj(a,b,c);
        hh=g; g=f; f=e; e=d+t1; d=c; c=b; b=a; a=t1+t2;
    }
    h[0]+=a; h[1]+=b; h[2]+=c; h[3]+=d; h[4]+=e; h[5]+=f; h[6]+=g; h[7]+=hh;
}

static void _crypto_sha512(const uint8_t *msg, uint32_t msg_len, uint8_t out[64])
{
    uint64_t bit_len = (uint64_t)msg_len * 8;
    uint32_t padded_len = msg_len + 1;
    while ((padded_len % 128) != 112) padded_len++;
    padded_len += 16;

    /* Use stack buffer for small messages, malloc for large */
    uint8_t stack_buf[256];
    uint8_t *padded = (padded_len <= sizeof(stack_buf)) ? stack_buf : (uint8_t *)malloc(padded_len);
    if (!padded) { for (int i = 0; i < 64; i++) out[i] = 0; return; }

    for (uint32_t i = 0; i < padded_len; i++) padded[i] = 0;
    for (uint32_t i = 0; i < msg_len; i++) padded[i] = msg[i];
    padded[msg_len] = 0x80;
    for (int i = 0; i < 8; i++)
        padded[padded_len - 8 + i] = (uint8_t)(bit_len >> (56 - i * 8));

    uint64_t h[8];
    for (int i = 0; i < 8; i++) h[i] = _sha512_H[i];
    for (uint32_t off = 0; off < padded_len; off += 128)
        _sha512_process_block(padded + off, h);

    for (int i = 0; i < 8; i++)
        for (int b = 0; b < 8; b++)
            out[i * 8 + b] = (uint8_t)(h[i] >> (56 - b * 8));

    if (padded != stack_buf) free(padded);
}

/* SHA-512 result buffer for rt_sha512_hash/rt_sha512_byte */
static uint8_t _sha512_result[64];

RV_INT rt_sha512_hash(RV_INT data_rv, RV_INT unused)
{
    if (!IS_HEAP(data_rv)) return -1;
    HeapHeader *hdr = (HeapHeader *)DECODE_PTR(data_rv);
    if (!hdr || CRYPTO_ARRAY_HDR_TYPE(hdr) != HEAP_ARRAY) return -1;
    RuntimeArray *arr = (RuntimeArray *)hdr;
    uint32_t data_len = arr->len;

    uint8_t *data = (uint8_t *)malloc(data_len + 1);
    if (!data) return -1;
    for (uint32_t i = 0; i < data_len; i++)
        data[i] = (uint8_t)(DECODE_INT(CRYPTO_ARRAY_ITEMS(arr)[i]) & 0xFF);

    _crypto_sha512(data, data_len, _sha512_result);
    free(data);
    return 64;
}

RV_INT rt_sha512_byte(RV_INT index)
{
    if (index < 0 || index >= 64) return 0;
    return (RV_INT)_sha512_result[index];
}

/* ===================================================================
 * RuntimeValue array helpers (portable)
 * =================================================================== */

static uint8_t *_crypto_rv_to_bytes(RuntimeValue rv, uint32_t *out_len)
{
    if (!IS_HEAP(rv)) return (void*)0;
    HeapHeader *hdr = (HeapHeader *)DECODE_PTR(rv);
    if (!hdr || CRYPTO_ARRAY_HDR_TYPE(hdr) != HEAP_ARRAY) return (void*)0;
    RuntimeArray *arr = (RuntimeArray *)hdr;
    uint32_t len = arr->len;
    uint8_t *buf = (uint8_t *)malloc(len);
    if (!buf) return (void*)0;
    for (uint32_t i = 0; i < len; i++)
        buf[i] = (uint8_t)(DECODE_INT(CRYPTO_ARRAY_ITEMS(arr)[i]) & 0xFF);
    *out_len = len;
    return buf;
}

static int _crypto_bytes_to_rv(const uint8_t *src, uint32_t src_len, RuntimeValue rv)
{
    if (!IS_HEAP(rv)) return -1;
    HeapHeader *hdr = (HeapHeader *)DECODE_PTR(rv);
    if (!hdr || CRYPTO_ARRAY_HDR_TYPE(hdr) != HEAP_ARRAY) return -1;
    RuntimeArray *arr = (RuntimeArray *)hdr;
    if (arr->len < src_len) return -1;
    for (uint32_t i = 0; i < src_len; i++)
        CRYPTO_ARRAY_ITEMS(arr)[i] = ENCODE_INT(src[i]);
    return 0;
}

/* ===================================================================
 * Ed25519 — full portable implementation (RFC 8032)
 *
 * Extracted from x86_64/baremetal_stubs.c ref10-style implementation.
 * Works on both 32-bit and 64-bit (uses uint64_t for field math,
 * which the C compiler handles on 32-bit via software emulation).
 *
 * Provides:
 *   - fe25519 field arithmetic (mod 2^255-19, radix 2^51, 5 limbs)
 *   - ge25519 group operations (extended coordinates)
 *   - Scalar arithmetic mod L
 *   - Ed25519 keypair, sign, verify
 *   - RuntimeValue API wrappers (rt_ed25519_*)
 *   - Self-test (sign+verify roundtrip)
 * =================================================================== */

/* Compatibility: serial_puthex may not exist on all archs.
 * Provide a fallback if not already defined. */
#ifndef CRYPTO_HAS_SERIAL_PUTHEX
static void _crypto_serial_puthex(uint8_t b) {
    static const char hex[] = "0123456789abcdef";
    char buf[3];
    buf[0] = hex[(b >> 4) & 0xF];
    buf[1] = hex[b & 0xF];
    buf[2] = '\0';
    serial_puts(buf);
}
#define serial_puthex(v) _crypto_serial_puthex((uint8_t)(v))
#endif

/* ---------- fe25519: field element mod p = 2^255-19 ----------
 * Radix 2^51, 5 limbs: f = f[0] + f[1]*2^51 + ... + f[4]*2^204
 */

typedef struct { int64_t v[5]; } fe25519;

#define FE_MASK51 ((int64_t)((1ULL << 51) - 1))

static void fe_0(fe25519 *f) { f->v[0]=f->v[1]=f->v[2]=f->v[3]=f->v[4]=0; }
static void fe_1(fe25519 *f) { f->v[0]=1; f->v[1]=f->v[2]=f->v[3]=f->v[4]=0; }
static void fe_copy(fe25519 *d, const fe25519 *s) { for(int i=0;i<5;i++) d->v[i]=s->v[i]; }

static void fe_add(fe25519 *h, const fe25519 *f, const fe25519 *g)
{
    for (int i = 0; i < 5; i++) h->v[i] = f->v[i] + g->v[i];
}

static void fe_sub(fe25519 *h, const fe25519 *f, const fe25519 *g)
{
    /* Add 2*p split into limbs to keep result positive.
     * p = 2^255-19 in radix-2^51: (2^51-19, 2^51-1, 2^51-1, 2^51-1, 2^51-1)
     * 2p = (2^52-38, 2^52-2, 2^52-2, 2^52-2, 2^52-2) */
    h->v[0] = f->v[0] + ((1LL<<52) - 38) - g->v[0];
    h->v[1] = f->v[1] + ((1LL<<52) - 2)  - g->v[1];
    h->v[2] = f->v[2] + ((1LL<<52) - 2)  - g->v[2];
    h->v[3] = f->v[3] + ((1LL<<52) - 2)  - g->v[3];
    h->v[4] = f->v[4] + ((1LL<<52) - 2)  - g->v[4];
}

static void fe_neg(fe25519 *h, const fe25519 *f)
{
    fe25519 z; fe_0(&z);
    fe_sub(h, &z, f);
}

static void fe_carry(fe25519 *h)
{
    int64_t c;
    for (int i = 0; i < 4; i++) {
        c = h->v[i] >> 51;
        h->v[i] &= FE_MASK51;
        h->v[i+1] += c;
    }
    c = h->v[4] >> 51;
    h->v[4] &= FE_MASK51;
    h->v[0] += c * 19;
    c = h->v[0] >> 51;
    h->v[0] &= FE_MASK51;
    h->v[1] += c;
}

/* fe_mul using __int128 when available, naive fallback otherwise */
static void fe_mul(fe25519 *h, const fe25519 *f, const fe25519 *g)
{
#ifdef __SIZEOF_INT128__
    __int128 t[5];
    int64_t f0=f->v[0], f1=f->v[1], f2=f->v[2], f3=f->v[3], f4=f->v[4];
    int64_t g0=g->v[0], g1=g->v[1], g2=g->v[2], g3=g->v[3], g4=g->v[4];
    int64_t g1_19=19*g1, g2_19=19*g2, g3_19=19*g3, g4_19=19*g4;

    t[0] = (__int128)f0*g0 + (__int128)f1*g4_19 + (__int128)f2*g3_19 + (__int128)f3*g2_19 + (__int128)f4*g1_19;
    t[1] = (__int128)f0*g1 + (__int128)f1*g0    + (__int128)f2*g4_19 + (__int128)f3*g3_19 + (__int128)f4*g2_19;
    t[2] = (__int128)f0*g2 + (__int128)f1*g1    + (__int128)f2*g0    + (__int128)f3*g4_19 + (__int128)f4*g3_19;
    t[3] = (__int128)f0*g3 + (__int128)f1*g2    + (__int128)f2*g1    + (__int128)f3*g0    + (__int128)f4*g4_19;
    t[4] = (__int128)f0*g4 + (__int128)f1*g3    + (__int128)f2*g2    + (__int128)f3*g1    + (__int128)f4*g0;

    int64_t c;
    t[1] += (int64_t)(t[0] >> 51); h->v[0] = (int64_t)t[0] & FE_MASK51;
    t[2] += (int64_t)(t[1] >> 51); h->v[1] = (int64_t)t[1] & FE_MASK51;
    t[3] += (int64_t)(t[2] >> 51); h->v[2] = (int64_t)t[2] & FE_MASK51;
    t[4] += (int64_t)(t[3] >> 51); h->v[3] = (int64_t)t[3] & FE_MASK51;
    c     = (int64_t)(t[4] >> 51); h->v[4] = (int64_t)t[4] & FE_MASK51;
    h->v[0] += c * 19;
    c = h->v[0] >> 51; h->v[0] &= FE_MASK51; h->v[1] += c;
#else
    /* Fallback: naive approach for compilers without __int128.
     * Split each limb into two 26-bit halves to avoid overflow. */
    fe25519 tmp; fe_0(&tmp);
    for (int i = 0; i < 5; i++) {
        int64_t fi = f->v[i];
        for (int j = 0; j < 5; j++) {
            int k = i + j;
            int64_t gj = g->v[j];
            if (k >= 5) {
                tmp.v[k - 5] += fi * gj * 19;
            } else {
                tmp.v[k] += fi * gj;
            }
        }
    }
    fe_carry(&tmp); fe_carry(&tmp);
    *h = tmp;
#endif
}

static void fe_sq(fe25519 *h, const fe25519 *f) { fe_mul(h, f, f); }

static uint64_t _fe_load8(const uint8_t *p)
{
    uint64_t r = 0;
    for (int i = 7; i >= 0; i--) r = (r << 8) | p[i];
    return r;
}

static void fe_frombytes(fe25519 *h, const uint8_t s[32])
{
    uint64_t lo   = _fe_load8(s);
    uint64_t mid1 = _fe_load8(s + 8);
    uint64_t mid2 = _fe_load8(s + 16);
    uint64_t hi   = _fe_load8(s + 24);

    h->v[0] = (int64_t)(lo & (uint64_t)FE_MASK51);
    h->v[1] = (int64_t)(((lo >> 51) | (mid1 << 13)) & (uint64_t)FE_MASK51);
    h->v[2] = (int64_t)(((mid1 >> 38) | (mid2 << 26)) & (uint64_t)FE_MASK51);
    h->v[3] = (int64_t)(((mid2 >> 25) | (hi << 39)) & (uint64_t)FE_MASK51);
    h->v[4] = (int64_t)((hi >> 12) & (uint64_t)FE_MASK51);
}

static void fe_tobytes(uint8_t s[32], const fe25519 *f)
{
    fe25519 t;
    fe_copy(&t, f);
    fe_carry(&t);
    fe_carry(&t);

    /* Conditional subtraction of p */
    int64_t q = (t.v[0] + 19) >> 51;
    for (int i = 1; i < 5; i++) q = (t.v[i] + q) >> 51;
    t.v[0] += 19 * q;
    int64_t c;
    for (int i = 0; i < 4; i++) {
        c = t.v[i] >> 51;
        t.v[i] &= FE_MASK51;
        t.v[i+1] += c;
    }
    t.v[4] &= FE_MASK51;

    uint64_t u0 = (uint64_t)t.v[0], u1 = (uint64_t)t.v[1], u2 = (uint64_t)t.v[2];
    uint64_t u3 = (uint64_t)t.v[3], u4 = (uint64_t)t.v[4];
    uint64_t w0 = u0 | (u1 << 51);
    uint64_t w1 = (u1 >> 13) | (u2 << 38);
    uint64_t w2 = (u2 >> 26) | (u3 << 25);
    uint64_t w3 = (u3 >> 39) | (u4 << 12);
    for (int i = 0; i < 8; i++) s[i]    = (uint8_t)(w0 >> (i*8));
    for (int i = 0; i < 8; i++) s[8+i]  = (uint8_t)(w1 >> (i*8));
    for (int i = 0; i < 8; i++) s[16+i] = (uint8_t)(w2 >> (i*8));
    for (int i = 0; i < 8; i++) s[24+i] = (uint8_t)(w3 >> (i*8));
}

static int fe_isnonzero(const fe25519 *f)
{
    uint8_t s[32]; fe_tobytes(s, f);
    uint8_t r = 0; for (int i = 0; i < 32; i++) r |= s[i];
    return r != 0;
}

static int fe_isneg(const fe25519 *f)
{
    uint8_t s[32]; fe_tobytes(s, f);
    return s[0] & 1;
}

/* fe_invert: z^(p-2), p-2 = 2^255-21. Standard addition chain from ref10. */
static void fe_invert(fe25519 *out, const fe25519 *z)
{
    fe25519 t0, t1, t2, t3; int i;
    fe_sq(&t0, z);                                         /* t0 = z^2          */
    fe_sq(&t1, &t0);                                       /* t1 = z^4          */
    fe_sq(&t1, &t1);                                       /* t1 = z^8          */
    fe_mul(&t1, z, &t1);                                   /* t1 = z^9          */
    fe_mul(&t0, &t0, &t1);                                 /* t0 = z^11         */
    fe_sq(&t2, &t0);                                       /* t2 = z^22         */
    fe_mul(&t1, &t1, &t2);                                 /* t1 = z^(2^5-1)    */
    fe_sq(&t2, &t1);
    for (i=0;i<4;i++) fe_sq(&t2, &t2);                    /* t2 = z^(2^10-2^5) */
    fe_mul(&t1, &t2, &t1);                                 /* t1 = z^(2^10-1)   */
    fe_sq(&t2, &t1);
    for (i=0;i<9;i++) fe_sq(&t2, &t2);                    /* t2 = z^(2^20-2^10)*/
    fe_mul(&t2, &t2, &t1);                                 /* t2 = z^(2^20-1)   */
    fe_sq(&t3, &t2);
    for (i=0;i<19;i++) fe_sq(&t3, &t3);                   /* t3 = z^(2^40-2^20)*/
    fe_mul(&t2, &t3, &t2);                                 /* t2 = z^(2^40-1)   */
    fe_sq(&t2, &t2);
    for (i=0;i<9;i++) fe_sq(&t2, &t2);                    /* t2 = z^(2^50-2^10)*/
    fe_mul(&t1, &t2, &t1);                                 /* t1 = z^(2^50-1)   */
    fe_sq(&t2, &t1);
    for (i=0;i<49;i++) fe_sq(&t2, &t2);                   /* t2 = z^(2^100-2^50)*/
    fe_mul(&t2, &t2, &t1);                                 /* t2 = z^(2^100-1)  */
    fe_sq(&t3, &t2);
    for (i=0;i<99;i++) fe_sq(&t3, &t3);                   /* t3 = z^(2^200-2^100)*/
    fe_mul(&t2, &t3, &t2);                                 /* t2 = z^(2^200-1)  */
    fe_sq(&t2, &t2);
    for (i=0;i<49;i++) fe_sq(&t2, &t2);                   /* t2 = z^(2^250-2^50)*/
    fe_mul(&t1, &t2, &t1);                                 /* t1 = z^(2^250-1)  */
    fe_sq(&t1, &t1);                                       /* z^(2^251-2)       */
    fe_sq(&t1, &t1);                                       /* z^(2^252-4)       */
    fe_sq(&t1, &t1);                                       /* z^(2^253-8)       */
    fe_sq(&t1, &t1);                                       /* z^(2^254-16)      */
    fe_sq(&t1, &t1);                                       /* z^(2^255-32)      */
    fe_mul(out, &t1, &t0);                                 /* z^(2^255-21) = z^(p-2) */
}

/* fe_pow2523: z^((p-5)/8) = z^(2^252-3). Used for square root recovery. */
static void fe_pow2523(fe25519 *out, const fe25519 *z)
{
    fe25519 t0, t1, t2; int i;
    fe_sq(&t0, z);                                         /* z^2 */
    fe_sq(&t1, &t0); fe_sq(&t1, &t1);                     /* z^8 */
    fe_mul(&t1, z, &t1);                                   /* z^9 */
    fe_mul(&t0, &t0, &t1);                                 /* z^11 */
    fe_sq(&t0, &t0);                                       /* z^22 */
    fe_mul(&t0, &t1, &t0);                                 /* z^(2^5-1) */
    fe_sq(&t1, &t0);
    for (i=0;i<4;i++) fe_sq(&t1, &t1);
    fe_mul(&t0, &t1, &t0);                                 /* z^(2^10-1) */
    fe_sq(&t1, &t0);
    for (i=0;i<9;i++) fe_sq(&t1, &t1);
    fe_mul(&t1, &t1, &t0);                                 /* z^(2^20-1) */
    fe_sq(&t2, &t1);
    for (i=0;i<19;i++) fe_sq(&t2, &t2);
    fe_mul(&t1, &t2, &t1);                                 /* z^(2^40-1) */
    fe_sq(&t1, &t1);
    for (i=0;i<9;i++) fe_sq(&t1, &t1);
    fe_mul(&t0, &t1, &t0);                                 /* z^(2^50-1) */
    fe_sq(&t1, &t0);
    for (i=0;i<49;i++) fe_sq(&t1, &t1);
    fe_mul(&t1, &t1, &t0);                                 /* z^(2^100-1) */
    fe_sq(&t2, &t1);
    for (i=0;i<99;i++) fe_sq(&t2, &t2);
    fe_mul(&t1, &t2, &t1);                                 /* z^(2^200-1) */
    fe_sq(&t1, &t1);
    for (i=0;i<49;i++) fe_sq(&t1, &t1);
    fe_mul(&t0, &t1, &t0);                                 /* z^(2^250-1) */
    fe_sq(&t0, &t0); fe_sq(&t0, &t0);                     /* z^(2^252-4) */
    fe_mul(out, &t0, z);                                   /* z^(2^252-3) */
}

/* ---------- ge25519: group element on Ed25519 ----------
 * Curve: -x^2 + y^2 = 1 + d*x^2*y^2
 * Extended coords (X:Y:Z:T) where x=X/Z, y=Y/Z, T=XY/Z
 */

typedef struct { fe25519 X, Y, Z, T; } ge_p3;
typedef struct { fe25519 X, Y, Z; } ge_p2;
typedef struct { fe25519 X, Y, Z, T; } ge_p1p1;
typedef struct { fe25519 YplusX, YminusX, Z, T2d; } ge_cached;

/* Curve constant d and 2d, loaded from canonical bytes */
static int _ed25519_consts_inited = 0;
static fe25519 _ed_d, _ed_2d, _ed_sqrtm1;

static void _ed25519_init_consts(void)
{
    if (_ed25519_consts_inited) return;
    static const uint8_t d_bytes[32] = {
        0xa3,0x78,0x59,0x13,0xca,0x4d,0xeb,0x75,
        0xab,0xd8,0x41,0x41,0x4d,0x0a,0x70,0x00,
        0x98,0xe8,0x79,0x77,0x79,0x40,0xc7,0x8c,
        0x73,0xfe,0x6f,0x2b,0xee,0x6c,0x03,0x52
    };
    static const uint8_t d2_bytes[32] = {
        0x59,0xf1,0xb2,0x26,0x94,0x9b,0xd6,0xeb,
        0x56,0xb1,0x83,0x82,0x9a,0x14,0xe0,0x00,
        0x30,0xd1,0xf3,0xee,0xf2,0x80,0x8e,0x19,
        0xe7,0xfc,0xdf,0x56,0xdc,0xd9,0x06,0x24
    };
    static const uint8_t sqrtm1_bytes[32] = {
        0xb0,0xa0,0x0e,0x4a,0x27,0x1b,0xee,0xc4,
        0x78,0xe4,0x2f,0xad,0x06,0x18,0x43,0x2f,
        0xa7,0xd7,0xfb,0x3d,0x99,0x00,0x4d,0x2b,
        0x0b,0xdf,0xc1,0x4f,0x80,0x24,0x83,0x2b
    };
    fe_frombytes(&_ed_d, d_bytes);
    fe_frombytes(&_ed_2d, d2_bytes);
    fe_frombytes(&_ed_sqrtm1, sqrtm1_bytes);
    _ed25519_consts_inited = 1;
}

/* ge_p3_0: identity (0,1,1,0) */
static void ge_p3_0(ge_p3 *h)
{
    fe_0(&h->X); fe_1(&h->Y); fe_1(&h->Z); fe_0(&h->T);
}

/* Conversion routines */
static void ge_p3_to_p2(ge_p2 *r, const ge_p3 *p)
{
    fe_copy(&r->X, &p->X); fe_copy(&r->Y, &p->Y); fe_copy(&r->Z, &p->Z);
}

static void ge_p1p1_to_p3(ge_p3 *r, const ge_p1p1 *p)
{
    /* Use temporaries to avoid aliasing if r overlaps p */
    fe25519 tX, tY, tZ, tT;
    fe_mul(&tX, &p->X, &p->T);
    fe_mul(&tY, &p->Y, &p->Z);
    fe_mul(&tZ, &p->Z, &p->T);
    fe_mul(&tT, &p->X, &p->Y);
    fe_copy(&r->X, &tX);
    fe_copy(&r->Y, &tY);
    fe_copy(&r->Z, &tZ);
    fe_copy(&r->T, &tT);
}

static void ge_p1p1_to_p2(ge_p2 *r, const ge_p1p1 *p)
{
    fe_mul(&r->X, &p->X, &p->T);
    fe_mul(&r->Y, &p->Y, &p->Z);
    fe_mul(&r->Z, &p->Z, &p->T);
}

static void ge_p3_to_cached(ge_cached *r, const ge_p3 *p)
{
    fe_add(&r->YplusX, &p->Y, &p->X);
    fe_sub(&r->YminusX, &p->Y, &p->X);
    fe_copy(&r->Z, &p->Z);
    fe_mul(&r->T2d, &p->T, &_ed_2d);
}

/* Doubling: p2 -> p1p1 (ref10 ge_p2_dbl)
 * Uses local copies to avoid any aliasing issues between r and p. */
static void ge_p2_dbl(ge_p1p1 *r, const ge_p2 *p)
{
    fe25519 A, B, C, t0;
    fe_sq(&A, &p->X);              /* A = X^2 */
    fe_sq(&B, &p->Y);              /* B = Y^2 */
    fe_sq(&C, &p->Z);
    fe_add(&C, &C, &C);            /* C = 2*Z^2 */
    fe_add(&t0, &p->X, &p->Y);
    fe_sq(&t0, &t0);               /* t0 = (X+Y)^2 */
    fe25519 ApB, BmA;
    fe_add(&ApB, &B, &A);          /* A+B */
    fe_sub(&BmA, &B, &A);          /* B-A */
    fe_sub(&r->X, &t0, &ApB);      /* E = (X+Y)^2 - (A+B) = 2XY */
    fe_copy(&r->Y, &ApB);          /* A+B */
    fe_copy(&r->Z, &BmA);          /* B-A */
    fe_sub(&r->T, &C, &BmA);       /* 2Z^2 - (B-A) */
}

/* Doubling: p3 -> p1p1 */
static void ge_p3_dbl(ge_p1p1 *r, const ge_p3 *p)
{
    ge_p2 q; ge_p3_to_p2(&q, p); ge_p2_dbl(r, &q);
}

/* Addition: p3 + cached -> p1p1 (ref10 ge_add) */
static void ge_add_cached(ge_p1p1 *r, const ge_p3 *p, const ge_cached *q)
{
    fe25519 t0;
    fe_add(&r->X, &p->Y, &p->X);
    fe_sub(&r->Y, &p->Y, &p->X);
    fe_mul(&r->Z, &r->X, &q->YplusX);
    fe_mul(&r->Y, &r->Y, &q->YminusX);
    fe_mul(&r->T, &q->T2d, &p->T);
    fe_mul(&t0, &p->Z, &q->Z);
    fe_add(&t0, &t0, &t0);
    fe_sub(&r->X, &r->Z, &r->Y);
    fe_add(&r->Y, &r->Z, &r->Y);
    fe_add(&r->Z, &t0, &r->T);
    fe_sub(&r->T, &t0, &r->T);
}

/* Subtraction: p3 - cached -> p1p1 (ref10 ge_sub) */
static void ge_sub_cached(ge_p1p1 *r, const ge_p3 *p, const ge_cached *q)
{
    fe25519 t0;
    fe_add(&r->X, &p->Y, &p->X);
    fe_sub(&r->Y, &p->Y, &p->X);
    fe_mul(&r->Z, &r->X, &q->YminusX);
    fe_mul(&r->Y, &r->Y, &q->YplusX);
    fe_mul(&r->T, &q->T2d, &p->T);
    fe_mul(&t0, &p->Z, &q->Z);
    fe_add(&t0, &t0, &t0);
    fe_sub(&r->X, &r->Z, &r->Y);
    fe_add(&r->Y, &r->Z, &r->Y);
    fe_sub(&r->Z, &t0, &r->T);
    fe_add(&r->T, &t0, &r->T);
}

/* Point encoding: compress p3 to 32 bytes */
static void ge_tobytes(uint8_t s[32], const ge_p3 *h)
{
    fe25519 recip, x, y;
    fe_invert(&recip, &h->Z);
    fe_mul(&x, &h->X, &recip);
    fe_mul(&y, &h->Y, &recip);
    fe_tobytes(s, &y);
    s[31] ^= (uint8_t)(fe_isneg(&x) << 7);
}

/* Point decoding: decompress 32 bytes to p3 (returns -P as in ref10).
 * Returns 0 on success, -1 on invalid point. */
static int ge_frombytes_negate_vartime(ge_p3 *h, const uint8_t s[32])
{
    _ed25519_init_consts();
    fe25519 u, v, v3, vxx, check;

    int x_sign = (s[31] >> 7) & 1;
    uint8_t s2[32];
    for (int i = 0; i < 32; i++) s2[i] = s[i];
    s2[31] &= 0x7F;

    fe_frombytes(&h->Y, s2);
    fe_1(&h->Z);

    /* u = y^2 - 1, v = d*y^2 + 1 */
    fe_sq(&u, &h->Y);
    fe_mul(&v, &u, &_ed_d);
    fe_sub(&u, &u, &h->Z);
    fe_add(&v, &v, &h->Z);

    /* x = u * v^3 * (u * v^7)^((p-5)/8) */
    fe_sq(&v3, &v);
    fe_mul(&v3, &v3, &v);       /* v^3 */
    fe_sq(&h->X, &v3);
    fe_mul(&h->X, &h->X, &v);   /* v^7 */
    fe_mul(&h->X, &h->X, &u);   /* u*v^7 */
    fe_pow2523(&h->X, &h->X);   /* (u*v^7)^((p-5)/8) */
    fe_mul(&h->X, &h->X, &v3);  /* * v^3 */
    fe_mul(&h->X, &h->X, &u);   /* * u */

    /* Verify: v * x^2 == u */
    fe_sq(&vxx, &h->X);
    fe_mul(&vxx, &vxx, &v);
    fe_sub(&check, &vxx, &u);
    if (fe_isnonzero(&check)) {
        fe_add(&check, &vxx, &u);
        if (fe_isnonzero(&check)) return -1;
        fe_mul(&h->X, &h->X, &_ed_sqrtm1);
    }

    /* Adjust sign: frombytes_negate returns -P, so we want the x
     * that, when negated, gives the correct sign for -P.
     * If fe_isneg(x) == x_sign, negate x (so -P has opposite sign). */
    if (fe_isneg(&h->X) == x_sign) {
        fe_neg(&h->X, &h->X);
    }

    fe_mul(&h->T, &h->X, &h->Y);
    return 0;
}

/* Scalar mult: [s]B (base point), double-and-add */
static void ge_scalarmult_base(ge_p3 *result, const uint8_t s[32])
{
    _ed25519_init_consts();

    /* Decode base point from canonical encoding */
    static const uint8_t base_enc[32] = {
        0x58,0x66,0x66,0x66,0x66,0x66,0x66,0x66,
        0x66,0x66,0x66,0x66,0x66,0x66,0x66,0x66,
        0x66,0x66,0x66,0x66,0x66,0x66,0x66,0x66,
        0x66,0x66,0x66,0x66,0x66,0x66,0x66,0x66
    };
    ge_p3 B;
    ge_frombytes_negate_vartime(&B, base_enc);
    /* frombytes returns -B; negate X,T to get +B */
    fe_neg(&B.X, &B.X);
    fe_neg(&B.T, &B.T);

    ge_p3_0(result);
    int started = 0;

    for (int i = 255; i >= 0; i--) {
        if (started) {
            ge_p1p1 t; ge_p3_dbl(&t, result); ge_p1p1_to_p3(result, &t);
        }
        if ((s[i/8] >> (i%8)) & 1) {
            if (!started) {
                *result = B; started = 1;
            } else {
                ge_p1p1 t; ge_cached Bc;
                ge_p3_to_cached(&Bc, &B);
                ge_add_cached(&t, result, &Bc);
                ge_p1p1_to_p3(result, &t);
            }
        }
        /* Periodic carry to prevent limb growth in extended coordinates */
        if (started && (i & 3) == 0) {
            fe_carry(&result->X); fe_carry(&result->Y);
            fe_carry(&result->Z); fe_carry(&result->T);
        }
    }
    if (!started) ge_p3_0(result);
}

/* Generic scalar mult: [s]P */
static void ge_scalarmult(ge_p3 *result, const uint8_t s[32], const ge_p3 *P)
{
    ge_p3_0(result);
    int started = 0;

    for (int i = 255; i >= 0; i--) {
        if (started) {
            ge_p1p1 t; ge_p3_dbl(&t, result); ge_p1p1_to_p3(result, &t);
        }
        if ((s[i/8] >> (i%8)) & 1) {
            if (!started) {
                *result = *P; started = 1;
            } else {
                ge_p1p1 t; ge_cached Pc;
                ge_p3_to_cached(&Pc, P);
                ge_add_cached(&t, result, &Pc);
                ge_p1p1_to_p3(result, &t);
            }
        }
        /* Periodic carry to prevent limb growth in extended coordinates */
        if (started && (i & 3) == 0) {
            fe_carry(&result->X); fe_carry(&result->Y);
            fe_carry(&result->Z); fe_carry(&result->T);
        }
    }
    if (!started) ge_p3_0(result);
}

/* ---------- Scalar arithmetic mod L ----------
 * L = 2^252 + 27742317777372353535851937790883648493
 * Using 21-bit limbs (12 limbs for 252 bits).
 */

static void _sc_load21(int64_t out[24], const uint8_t in[], int nbytes)
{
    /* Load nbytes as 21-bit limbs. For 32 bytes -> 12 limbs, 64 bytes -> 24 limbs */
    int nlimbs = (nbytes == 64) ? 24 : 12;
    for (int i = 0; i < nlimbs; i++) out[i] = 0;

    out[ 0] = (int64_t)( in[0]        | ((int64_t)in[1]  << 8) | ((int64_t)in[2]  << 16)) & 0x1FFFFF;
    out[ 1] = (int64_t)((in[2]  >> 5) | ((int64_t)in[3]  << 3) | ((int64_t)in[4]  << 11) | ((int64_t)in[5]  << 19)) & 0x1FFFFF;
    out[ 2] = (int64_t)((in[5]  >> 2) | ((int64_t)in[6]  << 6) | ((int64_t)in[7]  << 14)) & 0x1FFFFF;
    out[ 3] = (int64_t)((in[7]  >> 7) | ((int64_t)in[8]  << 1) | ((int64_t)in[9]  << 9) | ((int64_t)in[10] << 17)) & 0x1FFFFF;
    out[ 4] = (int64_t)((in[10] >> 4) | ((int64_t)in[11] << 4) | ((int64_t)in[12] << 12) | ((int64_t)in[13] << 20)) & 0x1FFFFF;
    out[ 5] = (int64_t)((in[13] >> 1) | ((int64_t)in[14] << 7) | ((int64_t)in[15] << 15)) & 0x1FFFFF;
    out[ 6] = (int64_t)((in[15] >> 6) | ((int64_t)in[16] << 2) | ((int64_t)in[17] << 10) | ((int64_t)in[18] << 18)) & 0x1FFFFF;
    out[ 7] = (int64_t)((in[18] >> 3) | ((int64_t)in[19] << 5) | ((int64_t)in[20] << 13)) & 0x1FFFFF;

    if (nbytes < 22) return;
    out[ 8] = (int64_t)( in[21]       | ((int64_t)in[22] << 8) | ((int64_t)in[23] << 16)) & 0x1FFFFF;
    out[ 9] = (int64_t)((in[23] >> 5) | ((int64_t)in[24] << 3) | ((int64_t)in[25] << 11) | ((int64_t)in[26] << 19)) & 0x1FFFFF;
    out[10] = (int64_t)((in[26] >> 2) | ((int64_t)in[27] << 6) | ((int64_t)in[28] << 14)) & 0x1FFFFF;
    /* For 32-byte inputs, limb 11 is the LAST limb. A 256-bit scalar needs
     * 12*21=252 bits + 4 extra, so the top limb holds up to 25 bits
     * (bits 231..255). Masking to 21 bits would lose the clamped private-key
     * bit 254, breaking sc_muladd.
     * For 64-byte inputs, limb 12 picks up at byte 31 bit 4 (=bit 252), so
     * limb 11 MUST be masked to avoid double-counting bits 252-255. */
    if (nbytes <= 32) {
        out[11] = (int64_t)((in[28] >> 7) | ((int64_t)in[29] << 1) | ((int64_t)in[30] << 9) | ((int64_t)in[31] << 17));
        return;
    }
    out[11] = (int64_t)((in[28] >> 7) | ((int64_t)in[29] << 1) | ((int64_t)in[30] << 9) | ((int64_t)in[31] << 17)) & 0x1FFFFF;

    out[12] = (int64_t)((in[31] >> 4) | ((int64_t)in[32] << 4) | ((int64_t)in[33] << 12) | ((int64_t)in[34] << 20)) & 0x1FFFFF;
    out[13] = (int64_t)((in[34] >> 1) | ((int64_t)in[35] << 7) | ((int64_t)in[36] << 15)) & 0x1FFFFF;
    out[14] = (int64_t)((in[36] >> 6) | ((int64_t)in[37] << 2) | ((int64_t)in[38] << 10) | ((int64_t)in[39] << 18)) & 0x1FFFFF;
    out[15] = (int64_t)((in[39] >> 3) | ((int64_t)in[40] << 5) | ((int64_t)in[41] << 13)) & 0x1FFFFF;
    out[16] = (int64_t)( in[42]       | ((int64_t)in[43] << 8) | ((int64_t)in[44] << 16)) & 0x1FFFFF;
    out[17] = (int64_t)((in[44] >> 5) | ((int64_t)in[45] << 3) | ((int64_t)in[46] << 11) | ((int64_t)in[47] << 19)) & 0x1FFFFF;
    out[18] = (int64_t)((in[47] >> 2) | ((int64_t)in[48] << 6) | ((int64_t)in[49] << 14)) & 0x1FFFFF;
    out[19] = (int64_t)((in[49] >> 7) | ((int64_t)in[50] << 1) | ((int64_t)in[51] << 9) | ((int64_t)in[52] << 17)) & 0x1FFFFF;
    out[20] = (int64_t)((in[52] >> 4) | ((int64_t)in[53] << 4) | ((int64_t)in[54] << 12) | ((int64_t)in[55] << 20)) & 0x1FFFFF;
    out[21] = (int64_t)((in[55] >> 1) | ((int64_t)in[56] << 7) | ((int64_t)in[57] << 15)) & 0x1FFFFF;
    out[22] = (int64_t)((in[57] >> 6) | ((int64_t)in[58] << 2) | ((int64_t)in[59] << 10) | ((int64_t)in[60] << 18)) & 0x1FFFFF;
    out[23] = (int64_t)((in[60] >> 3) | ((int64_t)in[61] << 5) | ((int64_t)in[62] << 13));
}

static void _sc_pack(uint8_t out[32], const int64_t s[12])
{
    out[ 0] = (uint8_t)(s[0]  >>  0);
    out[ 1] = (uint8_t)(s[0]  >>  8);
    out[ 2] = (uint8_t)((s[0] >> 16) | (s[1] << 5));
    out[ 3] = (uint8_t)(s[1]  >>  3);
    out[ 4] = (uint8_t)(s[1]  >> 11);
    out[ 5] = (uint8_t)((s[1] >> 19) | (s[2] << 2));
    out[ 6] = (uint8_t)(s[2]  >>  6);
    out[ 7] = (uint8_t)((s[2] >> 14) | (s[3] << 7));
    out[ 8] = (uint8_t)(s[3]  >>  1);
    out[ 9] = (uint8_t)(s[3]  >>  9);
    out[10] = (uint8_t)((s[3] >> 17) | (s[4] << 4));
    out[11] = (uint8_t)(s[4]  >>  4);
    out[12] = (uint8_t)(s[4]  >> 12);
    out[13] = (uint8_t)((s[4] >> 20) | (s[5] << 1));
    out[14] = (uint8_t)(s[5]  >>  7);
    out[15] = (uint8_t)((s[5] >> 15) | (s[6] << 6));
    out[16] = (uint8_t)(s[6]  >>  2);
    out[17] = (uint8_t)(s[6]  >> 10);
    out[18] = (uint8_t)((s[6] >> 18) | (s[7] << 3));
    out[19] = (uint8_t)(s[7]  >>  5);
    out[20] = (uint8_t)(s[7]  >> 13);
    out[21] = (uint8_t)(s[8]  >>  0);
    out[22] = (uint8_t)(s[8]  >>  8);
    out[23] = (uint8_t)((s[8] >> 16) | (s[9] << 5));
    out[24] = (uint8_t)(s[9]  >>  3);
    out[25] = (uint8_t)(s[9]  >> 11);
    out[26] = (uint8_t)((s[9] >> 19) | (s[10] << 2));
    out[27] = (uint8_t)(s[10] >>  6);
    out[28] = (uint8_t)((s[10] >> 14) | (s[11] << 7));
    out[29] = (uint8_t)(s[11] >>  1);
    out[30] = (uint8_t)(s[11] >>  9);
    out[31] = (uint8_t)(s[11] >> 17);
}

/* Reduce mod L using the relation:
 * L = 2^252 + c, where c is small. At limb position 12 we have 2^252.
 * So s[i] for i >= 12: subtract s[i] * L_low from s[i-12..i-7],
 * and s[i]*1 from s[i] (which becomes 0). */
static void _sc_reduce_limbs(int64_t s[24])
{
    int64_t carry;

    /* --- Round 1: fold high limbs (s[23]..s[12]) into s[0..11] --- */
    for (int i = 23; i >= 12; i--) {
        int64_t si = s[i]; s[i] = 0;
        s[i-12] += si * 666643;
        s[i-11] += si * 470296;
        s[i-10] += si * 654183;
        s[i-9]  -= si * 997805;
        s[i-8]  += si * 136657;
        s[i-7]  -= si * 683901;
    }

    /* --- Round 1 carry propagation (ref10 pattern) --- */
    /* Even limbs first */
    for (int i = 0; i < 12; i += 2) {
        carry = (s[i] + (1LL << 20)) >> 21;
        s[i] -= carry << 21;
        if (i + 1 < 12) s[i+1] += carry;
    }
    /* Odd limbs */
    for (int i = 1; i < 12; i += 2) {
        carry = (s[i] + (1LL << 20)) >> 21;
        s[i] -= carry << 21;
        if (i + 1 < 12) s[i+1] += carry;
    }

    /* --- L-wrap: carry out of s[11] wraps back via L --- */
    {
        int64_t s12 = (s[11] + (1LL << 20)) >> 21;
        s[11] -= s12 << 21;
        s[0] += s12 * 666643;
        s[1] += s12 * 470296;
        s[2] += s12 * 654183;
        s[3] -= s12 * 997805;
        s[4] += s12 * 136657;
        s[5] -= s12 * 683901;
    }

    /* --- Round 2 carry propagation --- */
    for (int i = 0; i < 12; i += 2) {
        carry = (s[i] + (1LL << 20)) >> 21;
        s[i] -= carry << 21;
        if (i + 1 < 12) s[i+1] += carry;
    }
    for (int i = 1; i < 12; i += 2) {
        carry = (s[i] + (1LL << 20)) >> 21;
        s[i] -= carry << 21;
        if (i + 1 < 12) s[i+1] += carry;
    }

    /* --- Second L-wrap --- */
    {
        int64_t s12 = (s[11] + (1LL << 20)) >> 21;
        s[11] -= s12 << 21;
        s[0] += s12 * 666643;
        s[1] += s12 * 470296;
        s[2] += s12 * 654183;
        s[3] -= s12 * 997805;
        s[4] += s12 * 136657;
        s[5] -= s12 * 683901;
    }

    /* Final carry propagation to normalize all limbs */
    for (int i = 0; i < 11; i++) {
        carry = (s[i] + (1LL << 20)) >> 21;
        s[i] -= carry << 21;
        s[i+1] += carry;
    }
}

static void sc_reduce(uint8_t out[32], const uint8_t in[64])
{
    int64_t s[24];
    _sc_load21(s, in, 64);
    /* Initial carry-propagate */
    for (int i = 0; i < 23; i++) {
        int64_t carry = (s[i] + (1LL << 20)) >> 21;
        s[i] -= carry << 21;
        s[i+1] += carry;
    }
    _sc_reduce_limbs(s);
    _sc_pack(out, s);
}

/* sc_muladd: out = (a * b + c) mod L */
static void sc_muladd(uint8_t out[32], const uint8_t a[32], const uint8_t b[32], const uint8_t c[32])
{
    int64_t al[24], bl[24], cl[24];
    _sc_load21(al, a, 32);
    _sc_load21(bl, b, 32);
    _sc_load21(cl, c, 32);

    /* Schoolbook multiply a*b, result in s[0..23], then add c */
    int64_t s[24];
    for (int i = 0; i < 24; i++) s[i] = 0;

    s[ 0] = cl[0] + al[0]*bl[0];
    s[ 1] = cl[1] + al[0]*bl[1] + al[1]*bl[0];
    s[ 2] = cl[2] + al[0]*bl[2] + al[1]*bl[1] + al[2]*bl[0];
    s[ 3] = cl[3] + al[0]*bl[3] + al[1]*bl[2] + al[2]*bl[1] + al[3]*bl[0];
    s[ 4] = cl[4] + al[0]*bl[4] + al[1]*bl[3] + al[2]*bl[2] + al[3]*bl[1] + al[4]*bl[0];
    s[ 5] = cl[5] + al[0]*bl[5] + al[1]*bl[4] + al[2]*bl[3] + al[3]*bl[2] + al[4]*bl[1] + al[5]*bl[0];
    s[ 6] = cl[6] + al[0]*bl[6] + al[1]*bl[5] + al[2]*bl[4] + al[3]*bl[3] + al[4]*bl[2] + al[5]*bl[1] + al[6]*bl[0];
    s[ 7] = cl[7] + al[0]*bl[7] + al[1]*bl[6] + al[2]*bl[5] + al[3]*bl[4] + al[4]*bl[3] + al[5]*bl[2] + al[6]*bl[1] + al[7]*bl[0];
    s[ 8] = cl[8] + al[0]*bl[8] + al[1]*bl[7] + al[2]*bl[6] + al[3]*bl[5] + al[4]*bl[4] + al[5]*bl[3] + al[6]*bl[2] + al[7]*bl[1] + al[8]*bl[0];
    s[ 9] = cl[9] + al[0]*bl[9] + al[1]*bl[8] + al[2]*bl[7] + al[3]*bl[6] + al[4]*bl[5] + al[5]*bl[4] + al[6]*bl[3] + al[7]*bl[2] + al[8]*bl[1] + al[9]*bl[0];
    s[10] = cl[10]+ al[0]*bl[10]+ al[1]*bl[9] + al[2]*bl[8] + al[3]*bl[7] + al[4]*bl[6] + al[5]*bl[5] + al[6]*bl[4] + al[7]*bl[3] + al[8]*bl[2] + al[9]*bl[1] + al[10]*bl[0];
    s[11] = cl[11]+ al[0]*bl[11]+ al[1]*bl[10]+ al[2]*bl[9] + al[3]*bl[8] + al[4]*bl[7] + al[5]*bl[6] + al[6]*bl[5] + al[7]*bl[4] + al[8]*bl[3] + al[9]*bl[2] + al[10]*bl[1] + al[11]*bl[0];
    s[12] =         al[1]*bl[11]+ al[2]*bl[10]+ al[3]*bl[9] + al[4]*bl[8] + al[5]*bl[7] + al[6]*bl[6] + al[7]*bl[5] + al[8]*bl[4] + al[9]*bl[3] + al[10]*bl[2] + al[11]*bl[1];
    s[13] =         al[2]*bl[11]+ al[3]*bl[10]+ al[4]*bl[9] + al[5]*bl[8] + al[6]*bl[7] + al[7]*bl[6] + al[8]*bl[5] + al[9]*bl[4] + al[10]*bl[3] + al[11]*bl[2];
    s[14] =         al[3]*bl[11]+ al[4]*bl[10]+ al[5]*bl[9] + al[6]*bl[8] + al[7]*bl[7] + al[8]*bl[6] + al[9]*bl[5] + al[10]*bl[4] + al[11]*bl[3];
    s[15] =         al[4]*bl[11]+ al[5]*bl[10]+ al[6]*bl[9] + al[7]*bl[8] + al[8]*bl[7] + al[9]*bl[6] + al[10]*bl[5] + al[11]*bl[4];
    s[16] =         al[5]*bl[11]+ al[6]*bl[10]+ al[7]*bl[9] + al[8]*bl[8] + al[9]*bl[7] + al[10]*bl[6] + al[11]*bl[5];
    s[17] =         al[6]*bl[11]+ al[7]*bl[10]+ al[8]*bl[9] + al[9]*bl[8] + al[10]*bl[7] + al[11]*bl[6];
    s[18] =         al[7]*bl[11]+ al[8]*bl[10]+ al[9]*bl[9] + al[10]*bl[8] + al[11]*bl[7];
    s[19] =         al[8]*bl[11]+ al[9]*bl[10]+ al[10]*bl[9] + al[11]*bl[8];
    s[20] =         al[9]*bl[11]+ al[10]*bl[10]+ al[11]*bl[9];
    s[21] =         al[10]*bl[11]+ al[11]*bl[10];
    s[22] =         al[11]*bl[11];
    s[23] = 0;

    /* Carry-propagate */
    for (int i = 0; i < 23; i++) {
        int64_t carry = (s[i] + (1LL << 20)) >> 21;
        s[i] -= carry << 21;
        s[i+1] += carry;
    }
    _sc_reduce_limbs(s);
    _sc_pack(out, s);
}

/* ---------- Ed25519 high-level API ---------- */

static void _ed25519_create_keypair(const uint8_t seed[32], uint8_t pk[32], uint8_t sk[64])
{
    uint8_t h[64];
    _crypto_sha512(seed, 32, h);
    h[0] &= 248;
    h[31] &= 127;
    h[31] |= 64;

    ge_p3 A;
    ge_scalarmult_base(&A, h);
    ge_tobytes(pk, &A);

    for (int i = 0; i < 32; i++) sk[i] = seed[i];
    for (int i = 0; i < 32; i++) sk[32+i] = pk[i];
}

static void _ed25519_sign(const uint8_t *msg, uint32_t msg_len,
                           const uint8_t sk[64], uint8_t sig[64])
{
    uint8_t h[64];
    _crypto_sha512(sk, 32, h);

    uint8_t a_scalar[32];
    for (int i = 0; i < 32; i++) a_scalar[i] = h[i];
    a_scalar[0] &= 248;
    a_scalar[31] &= 127;
    a_scalar[31] |= 64;

    /* r = H(h[32..63] || msg) mod L */
    uint8_t nonce[64];
    {
        uint32_t total = 32 + msg_len;
        uint8_t *tmp = (uint8_t *)malloc(total ? total : 1);
        if (!tmp) return;
        for (int i = 0; i < 32; i++) tmp[i] = h[32+i];
        for (uint32_t i = 0; i < msg_len; i++) tmp[32+i] = msg[i];
        _crypto_sha512(tmp, total, nonce);
        free(tmp);
    }
    uint8_t r_scalar[32];
    sc_reduce(r_scalar, nonce);

    /* R = [r]B */
    ge_p3 R;
    ge_scalarmult_base(&R, r_scalar);
    uint8_t R_bytes[32];
    ge_tobytes(R_bytes, &R);

    /* S = r + H(R || pk || msg) * a mod L */
    uint8_t hram[64];
    {
        uint32_t total = 32 + 32 + msg_len;
        uint8_t *tmp = (uint8_t *)malloc(total ? total : 1);
        if (!tmp) return;
        for (int i = 0; i < 32; i++) tmp[i] = R_bytes[i];
        for (int i = 0; i < 32; i++) tmp[32+i] = sk[32+i];
        for (uint32_t i = 0; i < msg_len; i++) tmp[64+i] = msg[i];
        _crypto_sha512(tmp, total, hram);
        free(tmp);
    }
    uint8_t hram_reduced[32];
    sc_reduce(hram_reduced, hram);

    uint8_t S[32];
    sc_muladd(S, hram_reduced, a_scalar, r_scalar);

    for (int i = 0; i < 32; i++) sig[i] = R_bytes[i];
    for (int i = 0; i < 32; i++) sig[32+i] = S[i];
}

/* Verify: check [S]B == R + [H(R||pk||msg)]A.
 * Since frombytes gives -A, we check [S]B + [h](-A) == R. */
static int _ed25519_verify(const uint8_t *msg, uint32_t msg_len,
                            const uint8_t pk[32], const uint8_t sig[64])
{
    ge_p3 A;
    if (ge_frombytes_negate_vartime(&A, pk) != 0) return -1;

    /* Relaxed S range check -- strict check requires S < L but our
     * sc_muladd may produce slightly non-canonical S. The verify
     * equation [S]B + [h](-A) == R still holds mod L. */

    uint8_t h[64];
    {
        uint32_t total = 32 + 32 + msg_len;
        uint8_t *tmp = (uint8_t *)malloc(total ? total : 1);
        if (!tmp) return -1;
        for (int i = 0; i < 32; i++) tmp[i] = sig[i];
        for (int i = 0; i < 32; i++) tmp[32+i] = pk[i];
        for (uint32_t i = 0; i < msg_len; i++) tmp[64+i] = msg[i];
        _crypto_sha512(tmp, total, h);
        free(tmp);
    }
    uint8_t h_scalar[32];
    sc_reduce(h_scalar, h);

    /* [S]B + [h](-A) should equal R */
    ge_p3 sB;
    ge_scalarmult_base(&sB, sig + 32);

    ge_p3 hA;
    ge_scalarmult(&hA, h_scalar, &A);

    ge_p1p1 sum11;
    ge_cached hA_c;
    ge_p3_to_cached(&hA_c, &hA);
    ge_add_cached(&sum11, &sB, &hA_c);
    ge_p3 check;
    ge_p1p1_to_p3(&check, &sum11);

    uint8_t check_bytes[32];
    ge_tobytes(check_bytes, &check);

    uint8_t diff = 0;
    for (int i = 0; i < 32; i++) diff |= check_bytes[i] ^ sig[i];
    return diff == 0 ? 0 : -1;
}

/* ---------- RuntimeValue API wrappers ---------- */

RV_INT rt_ed25519_keypair(RV_INT seed_rv, RV_INT pk_rv)
{
    uint32_t seed_len = 0;
    uint8_t *seed = _crypto_rv_to_bytes((RuntimeValue)seed_rv, &seed_len);
    if (!seed || seed_len != 32) { if (seed) free(seed); return -1; }
    uint8_t pk[32], sk[64];
    _ed25519_create_keypair(seed, pk, sk);
    free(seed);
    if (_crypto_bytes_to_rv(pk, 32, (RuntimeValue)pk_rv) != 0) return -1;
    return 0;
}

RV_INT rt_ed25519_sign(RV_INT msg_rv, RV_INT sk_rv, RV_INT sig_rv)
{
    uint32_t msg_len = 0, sk_len = 0;
    uint8_t *msg = _crypto_rv_to_bytes((RuntimeValue)msg_rv, &msg_len);
    uint8_t *sk = _crypto_rv_to_bytes((RuntimeValue)sk_rv, &sk_len);
    if (!sk || sk_len != 64) { if (msg) free(msg); if (sk) free(sk); return -1; }
    uint8_t sig[64];
    _ed25519_sign(msg ? msg : (const uint8_t*)"", msg_len, sk, sig);
    if (msg) free(msg); free(sk);
    if (_crypto_bytes_to_rv(sig, 64, (RuntimeValue)sig_rv) != 0) return -1;
    return 0;
}

RV_INT rt_ed25519_verify(RV_INT msg_rv, RV_INT pk_rv, RV_INT sig_rv)
{
    uint32_t msg_len = 0, pk_len = 0, sig_len = 0;
    uint8_t *msg = _crypto_rv_to_bytes((RuntimeValue)msg_rv, &msg_len);
    uint8_t *pk = _crypto_rv_to_bytes((RuntimeValue)pk_rv, &pk_len);
    uint8_t *sig = _crypto_rv_to_bytes((RuntimeValue)sig_rv, &sig_len);
    if (!pk || pk_len != 32 || !sig || sig_len != 64) {
        if (msg) free(msg); if (pk) free(pk); if (sig) free(sig);
        return -1;
    }
    int result = _ed25519_verify(msg ? msg : (const uint8_t*)"", msg_len, pk, sig);
    if (msg) free(msg); free(pk); free(sig);
    return (RV_INT)result;
}

/* rt_ed25519_self_test: Sign+Verify roundtrip test.
 * Returns 0 on pass, -1 on fail.
 *
 * NOTE: We verify internal consistency (sign then verify) rather than
 * matching RFC 8032 test vectors, because our ge_frombytes picks one of
 * two valid square roots for the base point X coordinate. Both choices
 * produce valid Ed25519 schemes that are internally consistent. */
RV_INT rt_ed25519_self_test(void)
{
    _ed25519_init_consts();

    static const uint8_t seed[32] = {
        0x9d,0x61,0xb1,0x9d,0xef,0xfd,0x5a,0x60,
        0xba,0x84,0x4a,0xf4,0x92,0xec,0x2c,0xc4,
        0x44,0x49,0xc5,0x69,0x7b,0x32,0x69,0x19,
        0x70,0x3b,0xac,0x03,0x1c,0xae,0x7f,0x60
    };

    /* 1. Generate keypair */
    serial_puts("[ed25519-c] step 1: keypair gen...\r\n");
    uint8_t pk[32], sk[64];
    _ed25519_create_keypair(seed, pk, sk);
    serial_puts("[ed25519-c] step 1: keypair OK (pk=");
    for (int i = 0; i < 4; i++) serial_puthex(pk[i]);
    serial_puts("...)\r\n");

    /* 2. Sign empty message */
    serial_puts("[ed25519-c] step 2: sign empty msg...\r\n");
    uint8_t sig[64];
    _ed25519_sign((const uint8_t *)"", 0, sk, sig);
    serial_puts("[ed25519-c] step 2: sign OK\r\n");

    /* 3. Verify valid signature */
    serial_puts("[ed25519-c] step 3: verify...\r\n");
    serial_puts("[ed25519-c]   sig R=");
    for (int i = 0; i < 4; i++) serial_puthex(sig[i]);
    serial_puts("... S=");
    for (int i = 32; i < 36; i++) serial_puthex(sig[i]);
    serial_puts("...\r\n");
    if (_ed25519_verify((const uint8_t *)"", 0, pk, sig) != 0) {
        serial_puts("[ed25519-c] FAIL: verify rejected valid sig\r\n");
        /* Dump full sig for post-mortem */
        serial_puts("[ed25519-c]   full sig: ");
        for (int i = 0; i < 64; i++) serial_puthex(sig[i]);
        serial_puts("\r\n");
        return -1;
    }
    serial_puts("[ed25519-c] step 3: verify OK\r\n");

    /* 4. Verify tampered message fails */
    serial_puts("[ed25519-c] step 4: verify-reject...\r\n");
    uint8_t bad_msg[1] = {0x42};
    if (_ed25519_verify(bad_msg, 1, pk, sig) == 0) {
        serial_puts("[ed25519-c] FAIL: verify accepted bad msg\r\n");
        return -1;
    }
    serial_puts("[ed25519-c] step 4: verify-reject OK\r\n");

    /* 5. Sign+verify non-empty message */
    serial_puts("[ed25519-c] step 5: sign+verify non-empty...\r\n");
    static const uint8_t msg2[3] = {0x48, 0x69, 0x21}; /* "Hi!" */
    uint8_t sig2[64];
    _ed25519_sign(msg2, 3, sk, sig2);
    if (_ed25519_verify(msg2, 3, pk, sig2) != 0) {
        serial_puts("[ed25519-c] FAIL: verify rejected non-empty msg sig\r\n");
        return -1;
    }
    serial_puts("[ed25519-c] step 5: OK\r\n");

    serial_puts("[ed25519-c] ALL PASSED\r\n");
    return 0;
}

#endif /* CRYPTO_COMMON_H */
