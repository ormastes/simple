/* rt_array_extend_i64 across packed layouts ([u8] BYTES, [u64] U64_PACKED)
 * and the generic tagged layout.
 *
 * Packed arrays store RAW elements; a generic array stores tagged words. The
 * element-wise fallback `rt_array_push(d, rt_array_get(s, i))` copies a slot
 * WORD verbatim, so mixing a [u64] with a generic array moved raw words into
 * tagged slots (raw 5 read back as a non-int) and tagged words into raw slots
 * (tagged 5 read back as 40). [u64] <-> [u64] copies whole host-order int64
 * words: both sides share one layout, so byte order never changes meaning.
 * Link against runtime_native.c (see the header of text_sort_selfcheck.c). */
#include "runtime.h"
#include <stdio.h>
#include <string.h>

extern int8_t rt_array_extend_i64(int64_t dst, int64_t src, int64_t count);

static unsigned checks;
#define CHECK(x) do { ++checks; if (!(x)) { fprintf(stderr, "FAIL line=%d check=%u\n", __LINE__, checks); return 1; } } while (0)
#define H(a) ((int64_t)(uintptr_t)(a))

int main(void) {
    const int64_t w[] = {5, 0x10, (int64_t)0x0102030405060708LL};

    /* [u64] -> [u64]: raw words survive, including a multiple of 8. */
    SplArray* u = rt_array_new_with_cap_u64(4);
    SplArray* v = rt_array_new_with_cap_u64(4);
    CHECK(u && v);
    for (int i = 0; i < 3; i++) CHECK(rt_array_push(u, w[i]));
    CHECK(rt_array_push(v, 9));
    CHECK(rt_array_extend_i64(H(v), H(u), 3));
    CHECK(rt_array_len(v) == 4);
    CHECK(rt_array_get(v, 0) == 9);
    for (int i = 0; i < 3; i++) CHECK(rt_array_get(v, i + 1) == w[i]);

    /* Self-extend: the source is re-read after any reallocation. */
    CHECK(rt_array_extend_i64(H(u), H(u), 3));
    CHECK(rt_array_len(u) == 6);
    for (int i = 0; i < 6; i++) CHECK(rt_array_get(u, i) == w[i % 3]);

    /* [u64] -> generic: each raw word becomes a tagged int. */
    SplArray* g = rt_array_new(2);
    CHECK(g);
    CHECK(rt_array_extend_i64(H(g), H(v), 2));
    CHECK(rt_array_len(g) == 2);
    CHECK(rt_array_get(g, 0) == rt_value_int(9));
    CHECK(rt_array_get(g, 1) == rt_value_int(5));

    /* generic -> [u64]: each tagged int is decoded to its raw word. */
    SplArray* t = rt_array_new(2);
    SplArray* r = rt_array_new_with_cap_u64(2);
    CHECK(t && r);
    CHECK(rt_array_push(t, rt_value_int(5)));
    CHECK(rt_array_push(t, rt_value_int(0x10)));
    CHECK(rt_array_extend_i64(H(r), H(t), 2));
    CHECK(rt_array_len(r) == 2);
    CHECK(rt_array_get(r, 0) == 5);
    CHECK(rt_array_get(r, 1) == 0x10);

    /* [u8] -> [u8] stays a raw byte copy; [u8] with [u64] is refused. */
    SplArray* b = rt_byte_array_new(2);
    SplArray* c = rt_byte_array_new(2);
    CHECK(b && c);
    CHECK(rt_array_push(b, rt_value_int(0x10)));
    CHECK(rt_array_push(b, rt_value_int(0x78)));
    CHECK(rt_array_extend_i64(H(c), H(b), 2));
    CHECK(rt_array_get(c, 0) == 0x10 && rt_array_get(c, 1) == 0x78);
    CHECK(!rt_array_extend_i64(H(r), H(b), 2));
    CHECK(rt_array_len(r) == 2);

    printf("PASS rt_array_extend_packed checks=%u u64_u64=1 self=1 u64_generic=1 generic_u64=1 bytes=1\n", checks);
    return 0;
}
