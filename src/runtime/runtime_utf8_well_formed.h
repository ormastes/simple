#ifndef SIMPLE_RUNTIME_UTF8_WELL_FORMED_H
#define SIMPLE_RUNTIME_UTF8_WELL_FORMED_H
/* Canonical UTF-8 well-formedness check (Unicode Table 3-7). Freestanding
 * safe: needs only <stddef.h>/<stdint.h>, declares no runtime symbols, so
 * the kernel runtimes (riscv64/x86_64 up_squared freestanding_runtime.c)
 * include it directly. Hosted strict text conversion lives in
 * runtime_utf8_strict_private.h; the Simple twin is _core_utf8_well_formed
 * in simple_core/core_array.spl. */
#include <stddef.h>
#include <stdint.h>

/* 1 when in[0..len) is well-formed UTF-8, else 0. Overlongs, stray
 * continuations, encoded surrogates, truncation and > U+10FFFF are 0. */
static inline int spl_utf8_well_formed(const uint8_t* in, size_t len) {
    size_t i = 0;
    while (i < len) {
        uint8_t b = in[i];
        size_t need;
        uint8_t lo = 0x80, hi = 0xBF;
        if (b < 0x80) { i++; continue; }
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
            return 0;
        }
        for (size_t j = 1; j <= need; j++) {
            if (i + j >= len || in[i + j] < lo || in[i + j] > hi) return 0;
            lo = 0x80; hi = 0xBF;
        }
        i += need + 1;
    }
    return 1;
}
#endif
