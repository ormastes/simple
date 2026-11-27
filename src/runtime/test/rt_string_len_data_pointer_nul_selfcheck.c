/* Real core-C test: rt_string_len on a raw `char*` that is the data member of a
 * live heap string must report the heap string's length, not strlen().
 *
 * Natively, `t!`, `match t: case Some(s)`, `if val s = t`, `t.unwrap()` and
 * `t ?? d` on a `text?` decode the payload with rt_interp_cstr, which yields
 * RtCoreString.data. strlen() on that cut binary-capable text at the first NUL
 * (SCV digested 4158 of 11465 bytes of identity_corrections.spl).
 * Bug doc: doc/08_tracking/bug/optional_text_unwrap_truncates_at_nul_2026-10-25.md
 *
 * Build/run (hosted): clang -O1 -I src/runtime -o rt_sl src/runtime/test/rt_string_len_data_pointer_nul_selfcheck.c src/runtime/runtime.c && ./rt_sl
 * Exit 0 = PASS. */
#include "../runtime_native.c"
#include <assert.h>

int main(void) {
    static const uint8_t bytes[5] = {'a', 'b', 0, 'c', 'd'};
    int64_t heap = rt_string_new(bytes, 5);
    assert(rt_string_len(heap) == 5);

    /* The unwrap decode: raw pointer into the registered string. */
    const char* raw = rt_interp_cstr(heap);
    assert(raw != NULL);
    assert(rt_string_len((int64_t)(uintptr_t)raw) == 5);
    /* Native `.len()` on a raw text local, and the rt_strlen + rt_string_new
     * re-tag, both go through rt_strlen. */
    assert(rt_strlen(raw) == 5);
    int64_t retagged = rt_string_new((const uint8_t*)raw, (uint64_t)rt_strlen(raw));
    assert(rt_string_len(retagged) == 5);

    /* Similar patterns: an unregistered C string still uses strlen, an
     * interior pointer (not the data start) is not mistaken for an owner, and
     * low addresses keep the -1 contract. */
    static const char literal[] = "hello";
    assert(rt_string_len((int64_t)(uintptr_t)literal) == 5);
    assert(rt_string_len((int64_t)(uintptr_t)(raw + 3)) == 2);
    assert(rt_string_len(0x100) == -1);

    /* Empty heap string: data pointer resolves to length 0. */
    int64_t empty = rt_string_new(bytes, 0);
    const char* empty_raw = rt_interp_cstr(empty);
    if (empty_raw) assert(rt_string_len((int64_t)(uintptr_t)empty_raw) == 0);

    printf("PASS rt_string_len data-pointer NUL selfcheck\n");
    return 0;
}
