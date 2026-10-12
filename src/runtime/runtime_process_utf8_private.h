#ifndef SIMPLE_PIPED_UTF8_STREAM_H
#define SIMPLE_PIPED_UTF8_STREAM_H
#include <stdint.h>
#include <stddef.h>
#include <string.h>
#define PIPED_RAW_CAP 8192U
#define PIPED_TEXT_CAP (3U * (PIPED_RAW_CAP + 3U))
struct PipedUtf8Tail { uint8_t bytes[3]; uint8_t len; };
/* Rust from_utf8_lossy's maximal-subpart policy, with an incomplete valid
 * suffix deferred until another read or EOF. NUL is an ordinary ASCII byte. */
static int piped_utf8_frame(struct PipedUtf8Tail* tail,
        const uint8_t* input, size_t len, int eof,
        uint8_t* out, size_t cap, size_t* written) {
    if (len > PIPED_RAW_CAP || tail->len > 3 || cap < 3U * (len + tail->len)) return 0;
    uint8_t bytes[PIPED_RAW_CAP + 3U];
    size_t total = tail->len + len;
    memcpy(bytes, tail->bytes, tail->len);
    if (len) memcpy(bytes + tail->len, input, len);
    struct PipedUtf8Tail next = {{0,0,0},0};
    size_t i = 0, used = 0;
    while (i < total) {
        uint8_t first = bytes[i];
        if (first < 0x80) { out[used++] = first; ++i; continue; }
        size_t width = 0;
        uint8_t second_min = 0x80, second_max = 0xbf;
        if (first >= 0xc2 && first <= 0xdf) width = 2;
        else if (first >= 0xe0 && first <= 0xef) {
            width = 3;
            if (first == 0xe0) second_min = 0xa0;
            if (first == 0xed) second_max = 0x9f;
        } else if (first >= 0xf0 && first <= 0xf4) {
            width = 4;
            if (first == 0xf0) second_min = 0x90;
            if (first == 0xf4) second_max = 0x8f;
        }
        size_t consumed = 1;
        int valid = width != 0, incomplete = 0;
        if (valid) {
            for (size_t j = 1; j < width; ++j) {
                if (i + j >= total) { incomplete = 1; consumed = j; break; }
                uint8_t byte = bytes[i+j];
                if ((j == 1 && (byte < second_min || byte > second_max)) ||
                    (j > 1 && (byte < 0x80 || byte > 0xbf))) {
                    valid = 0; consumed = j; break;
                }
            }
        }
        if (valid && incomplete && !eof) {
            next.len = (uint8_t)(total-i);
            memcpy(next.bytes, bytes+i, next.len);
            break;
        }
        if (valid && !incomplete) {
            memcpy(out+used, bytes+i, width); used += width; i += width;
        } else {
            out[used++] = 0xef; out[used++] = 0xbf; out[used++] = 0xbd;
            i += consumed;
        }
    }
    *tail = next; *written = used; return 1;
}
#endif
