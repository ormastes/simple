#ifndef SIMPLE_RUNTIME_UTF8_LOSSY_PRIVATE_H
#define SIMPLE_RUNTIME_UTF8_LOSSY_PRIVATE_H
/* Text is UTF-8. Bytes -> text conversion follows the Rust runtime's
 * String::from_utf8_lossy contract: each maximal ill-formed subsequence
 * becomes one U+FFFD (EF BF BD). `out` needs 3 * len bytes (worst case: every
 * input byte is its own ill-formed subsequence). Returns the output length. */
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

static size_t spl_utf8_lossy(const uint8_t* in, size_t len, uint8_t* out) {
    /* out == NULL: only measure. */
#define SPL_PUT(x) do { if (out) out[o] = (uint8_t)(x); o++; } while (0)
    size_t i = 0, o = 0;
    while (i < len) {
        uint8_t b = in[i];
        size_t need;
        uint8_t lo = 0x80, hi = 0xBF;
        if (b < 0x80) { SPL_PUT(b); i++; continue; }
        if (b >= 0xC2 && b <= 0xDF) need = 1;
        else if (b >= 0xE0 && b <= 0xEF) {
            need = 2;
            if (b == 0xE0) lo = 0xA0;
            else if (b == 0xED) hi = 0x9F;
        } else if (b >= 0xF0 && b <= 0xF4) {
            need = 3;
            if (b == 0xF0) lo = 0x90;
            else if (b == 0xF4) hi = 0x8F;
        } else {
            SPL_PUT(0xEF); SPL_PUT(0xBF); SPL_PUT(0xBD); i++; continue;
        }
        size_t j = 1;
        int ok = 1;
        for (; j <= need; j++) {
            if (i + j >= len || in[i + j] < lo || in[i + j] > hi) { ok = 0; break; }
            lo = 0x80; hi = 0xBF;
        }
        if (ok) {
            for (size_t k = 0; k <= need; k++) SPL_PUT(in[i + k]);
            i += need + 1;
        } else {
            SPL_PUT(0xEF); SPL_PUT(0xBF); SPL_PUT(0xBD);
            i += j; /* the valid prefix; the offending byte is re-examined */
        }
    }
    return o;
#undef SPL_PUT
}

extern int64_t rt_string_new(const uint8_t* data, uint64_t len);

/* [u8] data -> text value; valid input is copied once, invalid is repaired. */
static int64_t spl_text_from_utf8_lossy(const uint8_t* in, size_t len) {
    size_t n = spl_utf8_lossy(in, len, NULL);
    if (n == len) return rt_string_new(in, (uint64_t)len);
    uint8_t* buf = (uint8_t*)malloc(n);
    if (!buf) return rt_string_new(NULL, 0);
    spl_utf8_lossy(in, len, buf);
    int64_t r = rt_string_new(buf, (uint64_t)n);
    free(buf);
    return r;
}
#endif
