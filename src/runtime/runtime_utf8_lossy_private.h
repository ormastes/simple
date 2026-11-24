#ifndef SIMPLE_RUNTIME_UTF8_LOSSY_PRIVATE_H
#define SIMPLE_RUNTIME_UTF8_LOSSY_PRIVATE_H
/* Text is UTF-8. Bytes -> text conversion is STRICT (owner decision
 * 2026-11-23, utf8 rejection part 2): any ill-formed sequence -- overlong
 * form, lone/unexpected continuation byte, encoded surrogate, truncated
 * sequence, code point above U+10FFFF -- rejects the whole conversion with
 * NIL, exactly like the Rust runtime's `String::from_utf8` path. Nothing is
 * repaired to U+FFFD. Exact-byte carriers use rt_tls_wire_from_bytes; checked
 * callers use std.common.encoding.external_text.bytes_to_text_checked.
 * (File name kept for include stability; nothing here is lossy any more.) */
#include <stddef.h>
#include <stdint.h>

/* 1 when in[0..len) is well-formed UTF-8 (Unicode Table 3-7), else 0. */
static int spl_utf8_well_formed(const uint8_t* in, size_t len) {
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

extern int64_t rt_string_new(const uint8_t* data, uint64_t len);

#define SPL_UTF8_TEXT_REJECTED ((int64_t)3) /* RT_NIL == RuntimeValue::NIL */

/* [u8] data -> text value; valid input is copied once, invalid is NIL. */
static int64_t spl_text_from_utf8_strict(const uint8_t* in, size_t len) {
    if (!spl_utf8_well_formed(in, len)) return SPL_UTF8_TEXT_REJECTED;
    return rt_string_new(in, (uint64_t)len);
}
#endif
