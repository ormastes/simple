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
 * Ed25519 — portable implementation
 *
 * Full Ed25519 sign/verify using GF(2^255-19) arithmetic.
 * Works on both 32-bit and 64-bit (uses uint64_t for field math,
 * which the C compiler handles on 32-bit via software emulation).
 * =================================================================== */

/* Field element: 5 x uint64_t limbs (51 bits each) */
typedef struct { uint64_t v[5]; } fe25519;

static const uint64_t _FE_MASK = 0x7FFFFFFFFFFFFULL; /* 2^51 - 1 */

static fe25519 _fe_zero(void) { fe25519 r = {{0,0,0,0,0}}; return r; }
static fe25519 _fe_one(void) { fe25519 r = {{1,0,0,0,0}}; return r; }

static fe25519 _fe_add(fe25519 a, fe25519 b) {
    fe25519 r;
    for (int i = 0; i < 5; i++) r.v[i] = a.v[i] + b.v[i];
    return r;
}

static fe25519 _fe_sub(fe25519 a, fe25519 b) {
    /* Add 2*p to avoid underflow */
    static const uint64_t bias[5] = {0xFFFFFFFFFFFDAULL, 0xFFFFFFFFFFFFEULL, 0xFFFFFFFFFFFFEULL, 0xFFFFFFFFFFFFEULL, 0xFFFFFFFFFFFFEULL};
    fe25519 r;
    for (int i = 0; i < 5; i++) r.v[i] = (a.v[i] + bias[i]) - b.v[i];
    return r;
}

static fe25519 _fe_carry(fe25519 t) {
    uint64_t c;
    c = t.v[0] >> 51; t.v[0] &= _FE_MASK; t.v[1] += c;
    c = t.v[1] >> 51; t.v[1] &= _FE_MASK; t.v[2] += c;
    c = t.v[2] >> 51; t.v[2] &= _FE_MASK; t.v[3] += c;
    c = t.v[3] >> 51; t.v[3] &= _FE_MASK; t.v[4] += c;
    c = t.v[4] >> 51; t.v[4] &= _FE_MASK; t.v[0] += c * 19;
    return t;
}

static fe25519 _fe_mul(fe25519 a, fe25519 b) {
    uint64_t a0=a.v[0], a1=a.v[1], a2=a.v[2], a3=a.v[3], a4=a.v[4];
    uint64_t b0=b.v[0], b1=b.v[1], b2=b.v[2], b3=b.v[3], b4=b.v[4];
    uint64_t b1_19=b1*19, b2_19=b2*19, b3_19=b3*19, b4_19=b4*19;
    fe25519 r;
    r.v[0] = a0*b0 + a1*b4_19 + a2*b3_19 + a3*b2_19 + a4*b1_19;
    r.v[1] = a0*b1 + a1*b0 + a2*b4_19 + a3*b3_19 + a4*b2_19;
    r.v[2] = a0*b2 + a1*b1 + a2*b0 + a3*b4_19 + a4*b3_19;
    r.v[3] = a0*b3 + a1*b2 + a2*b1 + a3*b0 + a4*b4_19;
    r.v[4] = a0*b4 + a1*b3 + a2*b2 + a3*b1 + a4*b0;
    return _fe_carry(r);
}

static fe25519 _fe_sq(fe25519 a) { return _fe_mul(a, a); }

static fe25519 _fe_reduce(fe25519 a) {
    a = _fe_carry(a); a = _fe_carry(a);
    uint64_t c = (a.v[0]+19)>>51; c=(a.v[1]+c)>>51; c=(a.v[2]+c)>>51; c=(a.v[3]+c)>>51; c=(a.v[4]+c)>>51;
    a.v[0]+=19*c; c=a.v[0]>>51; a.v[0]&=_FE_MASK;
    a.v[1]+=c; c=a.v[1]>>51; a.v[1]&=_FE_MASK;
    a.v[2]+=c; c=a.v[2]>>51; a.v[2]&=_FE_MASK;
    a.v[3]+=c; c=a.v[3]>>51; a.v[3]&=_FE_MASK;
    a.v[4]+=c; a.v[4]&=_FE_MASK;
    return a;
}

static uint64_t _fe_load_le64(const uint8_t *p, int off) {
    uint64_t v = 0;
    for (int i = 0; i < 8; i++) {
        if (off + i < 32) v |= (uint64_t)p[off+i] << (i*8);
    }
    return v;
}

static fe25519 _fe_from_bytes(const uint8_t b[32]) {
    fe25519 r;
    r.v[0] = _fe_load_le64(b,0) & _FE_MASK;
    r.v[1] = (_fe_load_le64(b,6)>>3) & _FE_MASK;
    r.v[2] = (_fe_load_le64(b,12)>>6) & _FE_MASK;
    r.v[3] = (_fe_load_le64(b,19)>>1) & _FE_MASK;
    r.v[4] = (_fe_load_le64(b,24)>>12) & _FE_MASK;
    return r;
}

static void _fe_to_bytes(fe25519 a, uint8_t out[32]) {
    a = _fe_reduce(a);
    for (int i = 0; i < 32; i++) out[i] = 0;
    /* Pack 5 limbs into 32 bytes little-endian */
    uint64_t h0=a.v[0], h1=a.v[1], h2=a.v[2], h3=a.v[3], h4=a.v[4];
    uint64_t combined;
    combined = h0 | (h1 << 51);
    for (int i=0;i<7;i++) out[i] = (uint8_t)(combined>>(i*8));
    combined = (h1>>13) | (h2<<38);
    for (int i=0;i<7;i++) out[6+i] |= (uint8_t)(combined>>(i*8));
    combined = (h2>>26) | (h3<<25);
    for (int i=0;i<7;i++) out[12+i] |= (uint8_t)(combined>>(i*8));
    combined = (h3>>39) | (h4<<12);
    for (int i=0;i<8;i++) out[19+i] |= (uint8_t)(combined>>(i*8));
}

/* Forward declare: The Ed25519 internal crypto functions are large (~800 lines).
 * Rather than duplicate them here, we include the x86_64 implementation
 * which is already architecture-independent C code.
 *
 * The actual Ed25519 implementation remains in x86_64/baremetal_stubs.c
 * (lines ~3726-4753). For 32-bit ports, the same code can be extracted
 * or compiled separately — the internal math is all uint8_t/uint32_t/uint64_t.
 *
 * For now, this header provides the constant tables, SHA-512, and the
 * RuntimeValue wrappers. The Ed25519 functions are provided by a
 * separate #include or inline in each arch's baremetal_stubs.c.
 */

#endif /* CRYPTO_COMMON_H */
