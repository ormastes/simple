#include "../runtime.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#if defined(_WIN32)
#define WIN32_LEAN_AND_MEAN
#define NOMINMAX
#include <windows.h>
#endif

static int failures = 0;

static void check_digest(const uint8_t* input, size_t input_len,
                         const uint8_t expected[32]) {
    SplArray* bytes = rt_byte_array_new_len((uint64_t)input_len);
    for (size_t i = 0; i < input_len; i++) {
        if (!rt_bytes_u8_set(bytes, (int64_t)i, (int64_t)input[i])) {
            failures++;
            return;
        }
    }
    int64_t digest_value = rt_tls13_sha256((int64_t)(uintptr_t)bytes);
    SplArray* digest = (SplArray*)(uintptr_t)digest_value;
    if (rt_array_len(digest) != 32) {
        failures++;
        return;
    }
    for (int64_t i = 0; i < 32; i++) {
        if (rt_bytes_u8_at(digest, i) != expected[i]) {
            failures++;
            return;
        }
    }
}

/* SHA-384/512 (rt_sha384_digest / rt_sha512_digest) against FIPS 180-4
 * vectors. The 896-bit message is exactly 112 bytes, which takes the
 * two-block final padding path; one million 'a' (1000000 % 128 == 64) takes
 * the one-block path after 7812 full blocks. */
static int hex_nibble(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    return c - 'a' + 10;
}

static void check_sha2_512_family(int64_t (*digest_fn)(int64_t),
                                  const uint8_t* input, size_t input_len,
                                  const char* expected_hex) {
    size_t out_len = strlen(expected_hex) / 2u;
    SplArray* bytes = rt_byte_array_new_len((uint64_t)input_len);
    for (size_t i = 0; i < input_len; i++) {
        if (!rt_bytes_u8_set(bytes, (int64_t)i, (int64_t)input[i])) {
            failures++;
            return;
        }
    }
    SplArray* digest = (SplArray*)(uintptr_t)digest_fn((int64_t)(uintptr_t)bytes);
    if (rt_array_len(digest) != (int64_t)out_len) {
        failures++;
        return;
    }
    for (size_t i = 0; i < out_len; i++) {
        int64_t expected = (int64_t)((hex_nibble(expected_hex[2u * i]) << 4) |
                                     hex_nibble(expected_hex[2u * i + 1u]));
        if (rt_bytes_u8_at(digest, (int64_t)i) != expected) {
            failures++;
            return;
        }
    }
}

static void check_sha2_512_family_vectors(void) {
    static const char msg896[] =
        "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno"
        "ijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";
    static uint8_t million_a[1000000];
    memset(million_a, 'a', sizeof(million_a));

    check_sha2_512_family(rt_sha512_digest, NULL, 0,
        "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce"
        "47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e");
    check_sha2_512_family(rt_sha512_digest, (const uint8_t*)"abc", 3,
        "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a"
        "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f");
    check_sha2_512_family(rt_sha512_digest, (const uint8_t*)msg896, 112,
        "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018"
        "501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909");
    check_sha2_512_family(rt_sha512_digest, million_a, sizeof(million_a),
        "e718483d0ce769644e2e42c7bc15b4638e1f98b13b2044285632a803afa973eb"
        "de0ff244877ea60a4cb0432ce577c31beb009c5c2c49aa2e4eadb217ad8cc09b");
    check_sha2_512_family(rt_sha384_digest, NULL, 0,
        "38b060a751ac96384cd9327eb1b1e36a21fdb71114be0743"
        "4c0cc7bf63f6e1da274edebfe76f65fbd51ad2f14898b95b");
    check_sha2_512_family(rt_sha384_digest, (const uint8_t*)"abc", 3,
        "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded163"
        "1a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7");
    check_sha2_512_family(rt_sha384_digest, (const uint8_t*)msg896, 112,
        "09330c33f71147e83d192fc782cd1b4753111b173b3b05d2"
        "2fa08086e3b0f712fcc7c71a557e2db966c3e9fa91746039");
    check_sha2_512_family(rt_sha384_digest, million_a, sizeof(million_a),
        "9d0e1809716474cb086e834e310a4a1ced149e9c00f24852"
        "7972cec5704c2a5b07b8b3dc38ecc4ebae97ddd87f3d8985");
}

int main(void) {
    static const uint8_t empty_digest[32] = {
        0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14,
        0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
        0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c,
        0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55
    };
    static const uint8_t abc_digest[32] = {
        0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
        0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
        0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
        0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad
    };
    static const uint8_t abc[3] = {'a', 'b', 'c'};

    check_digest(NULL, 0, empty_digest);
    check_digest(abc, sizeof(abc), abc_digest);
    check_sha2_512_family_vectors();

#if defined(_WIN32)
    /* Windows has no clock_gettime/CLOCK_MONOTONIC; QueryPerformanceCounter is
     * the platform monotonic clock.  Same oracle: elapsed must be positive. */
    LARGE_INTEGER freq, before, after;
    if (!QueryPerformanceFrequency(&freq)) failures++;
    if (!QueryPerformanceCounter(&before)) failures++;
    rt_sleep_nanos(1000000);
    if (!QueryPerformanceCounter(&after)) failures++;
    int64_t elapsed_ns = freq.QuadPart > 0
        ? (int64_t)(((after.QuadPart - before.QuadPart) * 1000000000LL) / freq.QuadPart)
        : 0;
#else
    struct timespec before;
    struct timespec after;
    if (clock_gettime(CLOCK_MONOTONIC, &before) != 0) failures++;
    rt_sleep_nanos(1000000);
    if (clock_gettime(CLOCK_MONOTONIC, &after) != 0) failures++;
    int64_t elapsed_ns =
        (int64_t)(after.tv_sec - before.tv_sec) * 1000000000LL +
        (int64_t)(after.tv_nsec - before.tv_nsec);
#endif
    if (elapsed_ns <= 0) failures++;

    printf("SELFCHECK %s (%d failures)\n",
           failures == 0 ? "PASSED" : "FAILED", failures);
    return failures == 0 ? 0 : 1;
}
