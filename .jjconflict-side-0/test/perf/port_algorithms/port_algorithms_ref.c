#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>

#define DATA_SIZE 65536ULL
#define XXH_ITERS 1600ULL
#define CHACHA_ITERS 120ULL
#define CRC32_ITERS 160ULL
#define ADLER32_ITERS 800ULL

static uint64_t now_us(void) {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return (uint64_t)tv.tv_sec * 1000000ULL + (uint64_t)tv.tv_usec;
}

static uint64_t rotl64(uint64_t x, int r) { return (x << r) | (x >> (64 - r)); }
static uint32_t rotl32(uint32_t x, int r) { return (x << r) | (x >> (32 - r)); }

static uint64_t load64(const uint8_t *p) {
    uint64_t v;
    memcpy(&v, p, sizeof(v));
    return v;
}

static uint32_t load32(const uint8_t *p) {
    uint32_t v;
    memcpy(&v, p, sizeof(v));
    return v;
}

static uint64_t xxh64_round(uint64_t acc, uint64_t input) {
    const uint64_t p1 = 0x9E3779B185EBCA87ULL;
    const uint64_t p2 = 0xC2B2AE3D27D4EB4FULL;
    acc += input * p2;
    acc = rotl64(acc, 31);
    return acc * p1;
}

static uint64_t xxh64_merge(uint64_t acc, uint64_t val) {
    const uint64_t p1 = 0x9E3779B185EBCA87ULL;
    const uint64_t p4 = 0x85EBCA77C2B2AE63ULL;
    acc ^= xxh64_round(0, val);
    return acc * p1 + p4;
}

static uint64_t xxh64_avalanche(uint64_t h) {
    h ^= h >> 33;
    h *= 0xC2B2AE3D27D4EB4FULL;
    h ^= h >> 29;
    h *= 0x165667B19E3779F9ULL;
    h ^= h >> 32;
    return h;
}

static uint64_t xxhash64_ref(const uint8_t *data, size_t len, uint64_t seed) {
    const uint64_t p1 = 0x9E3779B185EBCA87ULL;
    const uint64_t p2 = 0xC2B2AE3D27D4EB4FULL;
    const uint64_t p3 = 0x165667B19E3779F9ULL;
    const uint64_t p4 = 0x85EBCA77C2B2AE63ULL;
    const uint64_t p5 = 0x27D4EB2F165667C5ULL;
    size_t pos = 0;
    uint64_t h;
    if (len >= 32) {
        uint64_t v1 = seed + p1 + p2;
        uint64_t v2 = seed + p2;
        uint64_t v3 = seed;
        uint64_t v4 = seed - p1;
        size_t limit = len - 31;
        while (pos < limit) {
            v1 = xxh64_round(v1, load64(data + pos)); pos += 8;
            v2 = xxh64_round(v2, load64(data + pos)); pos += 8;
            v3 = xxh64_round(v3, load64(data + pos)); pos += 8;
            v4 = xxh64_round(v4, load64(data + pos)); pos += 8;
        }
        h = rotl64(v1, 1) + rotl64(v2, 7) + rotl64(v3, 12) + rotl64(v4, 18);
        h = xxh64_merge(h, v1);
        h = xxh64_merge(h, v2);
        h = xxh64_merge(h, v3);
        h = xxh64_merge(h, v4);
    } else {
        h = seed + p5;
    }
    h += len;
    while (pos + 8 <= len) {
        uint64_t k = xxh64_round(0, load64(data + pos));
        h ^= k;
        h = rotl64(h, 27) * p1 + p4;
        pos += 8;
    }
    if (pos + 4 <= len) {
        h ^= (uint64_t)load32(data + pos) * p1;
        h = rotl64(h, 23) * p2 + p3;
        pos += 4;
    }
    while (pos < len) {
        h ^= (uint64_t)data[pos] * p5;
        h = rotl64(h, 11) * p1;
        pos++;
    }
    return xxh64_avalanche(h);
}

static uint32_t crc32_ref(const uint8_t *data, size_t len) {
    uint32_t table[256];
    for (uint32_t i = 0; i < 256; i++) {
        uint32_t crc = i;
        for (uint32_t bit = 0; bit < 8; bit++) {
            crc = (crc & 1U) ? ((crc >> 1) ^ 0xEDB88320U) : (crc >> 1);
        }
        table[i] = crc;
    }

    uint32_t crc = 0xFFFFFFFFU;
    for (size_t i = 0; i < len; i++) {
        crc = (crc >> 8) ^ table[(crc ^ data[i]) & 0xFFU];
    }
    return crc ^ 0xFFFFFFFFU;
}

static uint32_t adler32_ref(const uint8_t *data, size_t len) {
    uint32_t a = 1U;
    uint32_t b = 0U;
    size_t i = 0;
    while (i < len) {
        size_t end = i + 5552U;
        if (end > len) end = len;
        while (i < end) {
            a += data[i++];
            b += a;
        }
        a %= 65521U;
        b %= 65521U;
    }
    return (b << 16) | a;
}

static void qr(uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d) {
    *a += *b; *d = rotl32(*d ^ *a, 16);
    *c += *d; *b = rotl32(*b ^ *c, 12);
    *a += *b; *d = rotl32(*d ^ *a, 8);
    *c += *d; *b = rotl32(*b ^ *c, 7);
}

static void chacha_block(const uint8_t key[32], uint32_t counter, const uint8_t nonce[12], uint8_t out[64]) {
    uint32_t s[16] = {
        0x61707865U, 0x3320646eU, 0x79622d32U, 0x6b206574U,
        load32(key), load32(key + 4), load32(key + 8), load32(key + 12),
        load32(key + 16), load32(key + 20), load32(key + 24), load32(key + 28),
        counter, load32(nonce), load32(nonce + 4), load32(nonce + 8)
    };
    uint32_t x[16];
    memcpy(x, s, sizeof(x));
    for (int i = 0; i < 10; i++) {
        qr(&x[0], &x[4], &x[8], &x[12]);
        qr(&x[1], &x[5], &x[9], &x[13]);
        qr(&x[2], &x[6], &x[10], &x[14]);
        qr(&x[3], &x[7], &x[11], &x[15]);
        qr(&x[0], &x[5], &x[10], &x[15]);
        qr(&x[1], &x[6], &x[11], &x[12]);
        qr(&x[2], &x[7], &x[8], &x[13]);
        qr(&x[3], &x[4], &x[9], &x[14]);
    }
    for (int i = 0; i < 16; i++) {
        uint32_t w = x[i] + s[i];
        out[i * 4 + 0] = (uint8_t)w;
        out[i * 4 + 1] = (uint8_t)(w >> 8);
        out[i * 4 + 2] = (uint8_t)(w >> 16);
        out[i * 4 + 3] = (uint8_t)(w >> 24);
    }
}

static void chacha_encrypt(const uint8_t key[32], uint32_t counter, const uint8_t nonce[12], const uint8_t *in, uint8_t *out, size_t len) {
    uint8_t block[64];
    size_t pos = 0;
    while (pos < len) {
        chacha_block(key, counter++, nonce, block);
        for (size_t j = 0; j < 64 && pos < len; j++, pos++) out[pos] = in[pos] ^ block[j];
    }
}

static uint64_t checksum_bytes(const uint8_t *data, size_t len) {
    uint64_t sum = 0;
    for (size_t i = 0; i < len; i++) sum = ((sum << 5) ^ (sum >> 2)) + data[i];
    return sum;
}

static void report(const char *alg, uint64_t bytes, uint64_t iters, uint64_t micros, uint64_t checksum) {
    if (micros == 0) micros = 1;
    printf("[algbench] lang=c alg=%s bytes=%llu iters=%llu micros=%llu mbps=%llu checksum=%llu\n",
           alg, (unsigned long long)bytes, (unsigned long long)iters,
           (unsigned long long)micros, (unsigned long long)((bytes * iters) / micros),
           (unsigned long long)checksum);
}

int main(void) {
    uint8_t *data = malloc(DATA_SIZE);
    uint8_t *out = malloc(DATA_SIZE);
    uint8_t key[32];
    uint8_t nonce[12] = {0,0,0,9,0,0,0,0x4a,0,0,0,0};
    for (uint64_t i = 0; i < DATA_SIZE; i++) data[i] = (uint8_t)((i * 131 + 17) & 0xff);
    for (int i = 0; i < 32; i++) key[i] = (uint8_t)i;

    uint64_t checksum = 0;
    uint64_t start = now_us();
    for (uint64_t i = 0; i < XXH_ITERS; i++) checksum ^= xxhash64_ref(data, DATA_SIZE, i);
    report("xxhash64", DATA_SIZE, XXH_ITERS, now_us() - start, checksum);

    checksum = 0;
    start = now_us();
    for (uint64_t i = 0; i < CRC32_ITERS; i++) checksum ^= ((uint64_t)crc32_ref(data, DATA_SIZE) + i);
    report("crc32", DATA_SIZE, CRC32_ITERS, now_us() - start, checksum);

    checksum = 0;
    start = now_us();
    for (uint64_t i = 0; i < ADLER32_ITERS; i++) checksum ^= ((uint64_t)adler32_ref(data, DATA_SIZE) + i);
    report("adler32", DATA_SIZE, ADLER32_ITERS, now_us() - start, checksum);

    checksum = 0;
    start = now_us();
    for (uint64_t i = 0; i < CHACHA_ITERS; i++) {
        chacha_encrypt(key, (uint32_t)i, nonce, data, out, DATA_SIZE);
        checksum ^= checksum_bytes(out, DATA_SIZE);
    }
    report("chacha20", DATA_SIZE, CHACHA_ITERS, now_us() - start, checksum);

    free(out);
    free(data);
    return 0;
}
