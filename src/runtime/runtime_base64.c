#include <stdint.h>
#include <stddef.h>

static const char ENCODE_TABLE[64] =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

static const uint8_t DECODE_TABLE[128] = {
    255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,
    255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,
    255,255,255,255,255,255,255,255,255,255,255, 62,255,255,255, 63,
     52, 53, 54, 55, 56, 57, 58, 59, 60, 61,255,255,255,  0,255,255,
    255,  0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14,
     15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,255,255,255,255,255,
    255, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40,
     41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51,255,255,255,255,255,
};

int64_t __c_rt_base64_encode(const uint8_t *input, uint64_t input_len, uint8_t *output, uint64_t output_cap) {
    if (!input && input_len > 0) return -1;
    uint64_t needed = ((input_len + 2) / 3) * 4;
    if (needed > output_cap) return -1;

    uint64_t i = 0, o = 0;
    while (i < input_len) {
        uint8_t b1 = input[i];
        uint8_t b2 = (i + 1 < input_len) ? input[i + 1] : 0;
        uint8_t b3 = (i + 2 < input_len) ? input[i + 2] : 0;

        output[o++] = ENCODE_TABLE[b1 >> 2];
        output[o++] = ENCODE_TABLE[((b1 & 0x03) << 4) | (b2 >> 4)];
        output[o++] = (i + 1 < input_len) ? ENCODE_TABLE[((b2 & 0x0F) << 2) | (b3 >> 6)] : '=';
        output[o++] = (i + 2 < input_len) ? ENCODE_TABLE[b3 & 0x3F] : '=';

        i += 3;
    }
    return (int64_t)o;
}

int64_t __c_rt_base64_decode(const uint8_t *input, uint64_t input_len, uint8_t *output, uint64_t output_cap) {
    if (!input && input_len > 0) return -1;

    uint64_t o = 0;
    uint8_t chunk[4];
    int chunk_len = 0;
    int pad_count = 0;

    for (uint64_t i = 0; i < input_len; i++) {
        uint8_t c = input[i];
        if (c == ' ' || c == '\t' || c == '\n' || c == '\r') continue;

        if (c == '=') {
            chunk[chunk_len++] = 0;
            pad_count++;
        } else if (c < 128 && DECODE_TABLE[c] != 255) {
            chunk[chunk_len++] = DECODE_TABLE[c];
        } else {
            continue;
        }

        if (chunk_len == 4) {
            if (o + 3 > output_cap) return -1;
            output[o++] = (chunk[0] << 2) | (chunk[1] >> 4);
            if (pad_count < 2) output[o++] = (chunk[1] << 4) | (chunk[2] >> 2);
            if (pad_count < 1) output[o++] = (chunk[2] << 6) | chunk[3];
            chunk_len = 0;
            pad_count = 0;
        }
    }

    if (chunk_len >= 2) {
        if (o + 1 > output_cap) return -1;
        output[o++] = (chunk[0] << 2) | (chunk[1] >> 4);
    }
    if (chunk_len >= 3) {
        if (o + 1 > output_cap) return -1;
        output[o++] = (chunk[1] << 4) | (chunk[2] >> 2);
    }

    return (int64_t)o;
}
