/* x86_64 freestanding text accessors — no allocation, no libc.
 *
 * Semantics mirror the hosted runtime (src/runtime/runtime_native.c
 * rt_string_char_code_at / rt_string_byte_at) and the aarch64 freestanding
 * runtime: char_code_at is CODEPOINT-indexed over UTF-8, byte_at is
 * BYTE-indexed; out of range -> 0. Host-tested by
 * test/01_unit/runtime/x86_64_freestanding_char_code_at_test.c. */
#ifndef X86_64_TEXT_CODEPOINT_H
#define X86_64_TEXT_CODEPOINT_H

#include <stdint.h>

static inline uint64_t x64_text_cstr_len(const unsigned char *data) {
    uint64_t n = 0;
    while (data[n] != 0) n++;
    return n;
}

static inline int64_t x64_text_code_at(const unsigned char *data, uint64_t len, int64_t index) {
    uint64_t byte_index = 0;
    uint64_t char_index = 0;
    if (!data || index < 0) return 0;
    while (byte_index < len) {
        unsigned char b0 = data[byte_index];
        uint64_t width = 1;
        int64_t code = b0;
        if (b0 >= 194 && b0 <= 223 && byte_index + 1 < len) {
            width = 2;
            code = ((int64_t)(b0 & 31) << 6) | (data[byte_index + 1] & 63);
        } else if (b0 >= 224 && b0 <= 239 && byte_index + 2 < len) {
            width = 3;
            code = ((int64_t)(b0 & 15) << 12) | ((int64_t)(data[byte_index + 1] & 63) << 6) | (data[byte_index + 2] & 63);
        } else if (b0 >= 240 && b0 <= 244 && byte_index + 3 < len) {
            width = 4;
            code = ((int64_t)(b0 & 7) << 18) | ((int64_t)(data[byte_index + 1] & 63) << 12) | ((int64_t)(data[byte_index + 2] & 63) << 6) | (data[byte_index + 3] & 63);
        }
        if (char_index == (uint64_t)index) return code;
        byte_index += width;
        char_index += 1;
    }
    return 0;
}

static inline int64_t x64_text_byte_at(const unsigned char *data, uint64_t len, int64_t index) {
    if (!data || index < 0 || (uint64_t)index >= len) return 0;
    return data[index];
}

#endif
