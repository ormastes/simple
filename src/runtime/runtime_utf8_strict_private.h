#ifndef SIMPLE_RUNTIME_UTF8_STRICT_PRIVATE_H
#define SIMPLE_RUNTIME_UTF8_STRICT_PRIVATE_H
/* Text is UTF-8. Bytes -> text conversion is STRICT (owner decision
 * 2026-11-23, utf8 rejection part 2): any ill-formed sequence -- overlong
 * form, lone/unexpected continuation byte, encoded surrogate, truncated
 * sequence, code point above U+10FFFF -- rejects the whole conversion with
 * NIL, exactly like the Rust runtime's `String::from_utf8` path. Nothing is
 * repaired to U+FFFD. Exact-byte carriers use rt_tls_wire_from_bytes; checked
 * callers use std.common.encoding.external_text.bytes_to_text_checked. */
#include "runtime_utf8_well_formed.h"

extern int64_t rt_string_new(const uint8_t* data, uint64_t len);

#define SPL_UTF8_TEXT_REJECTED ((int64_t)3) /* RT_NIL == RuntimeValue::NIL */

/* [u8] data -> text value; valid input is copied once, invalid is NIL. */
static int64_t spl_text_from_utf8_strict(const uint8_t* in, size_t len) {
    if (!spl_utf8_well_formed(in, len)) return SPL_UTF8_TEXT_REJECTED;
    return rt_string_new(in, (uint64_t)len);
}
#endif
