/* OrderedMap erased-key boundary. Link against the real runtime_native.c. */
#include "runtime.h"
#include <assert.h>
#include <stdint.h>
#include <string.h>

static int64_t str(const char* value) {
    return rt_string_new((const uint8_t*)value, (uint64_t)strlen(value));
}

int main(void) {
    assert(spl_ordered_key_cmp(rt_value_int(-5), rt_value_int(8)) < 0);
    assert(spl_ordered_key_cmp(rt_value_int(8), rt_value_int(-5)) > 0);
    assert(spl_ordered_key_cmp(rt_value_int(8), rt_value_int(8)) == 0);
    assert(spl_ordered_key_cmp(9, 17) < 0); /* raw scalar words alias heap tag bits */
    assert(spl_ordered_key_cmp(10, 18) < 0); /* raw scalar words alias float tag bits */
    assert(spl_ordered_key_cmp(18, 10) > 0);
    assert(spl_ordered_key_cmp(10, rt_value_int(3)) > 0);
    assert(spl_ordered_key_cmp(rt_value_int(3), 10) < 0);

    int64_t wide_low = rt_value_int(INT64_C(1152921504606846976));
    int64_t wide_high = rt_value_int(INT64_C(1152921504606846977));
    assert(spl_ordered_key_cmp(wide_low, wide_high) < 0);
    assert(spl_ordered_key_cmp(rt_value_int(7), wide_low) < 0);
    assert(spl_ordered_key_cmp(wide_low, rt_value_int(7)) > 0);
    assert(spl_ordered_key_cmp(wide_low, 9) > 0);
    assert(spl_ordered_key_cmp(rt_value_u64(INT64_MAX), rt_value_u64(INT64_MAX - 1)) > 0);
    assert(spl_ordered_key_cmp(wide_low, rt_value_u64(INT64_MAX)) == 2);
    assert(spl_ordered_key_cmp(rt_value_u64(INT64_MAX), wide_low) == 2);

    assert(spl_ordered_key_cmp(str("alpha"), str("beta")) < 0);
    assert(spl_ordered_key_cmp(str("a"), str("c")) < 0);
    assert(spl_ordered_key_cmp(str("same"), str("same")) == 0);
    assert(spl_ordered_key_cmp(rt_dict_new(8), rt_dict_new(8)) == 2);
    assert(spl_ordered_key_cmp(str("text"), rt_value_int(1)) == 2);

    /* Erased-key hash: equal keys hash equally, text by content (FNV-1a,
     * = std.hash `impl Hash for text`), integers by value (= Hash for i64). */
    int64_t hash_a = str("equal text");
    int64_t hash_b = str("equal text");
    assert(hash_a != hash_b);
    assert(spl_erased_key_hash(hash_a) == spl_erased_key_hash(hash_b));
    assert(spl_erased_key_hash(hash_a) == rt_hash_text(hash_a));
    assert(spl_erased_key_hash(str("")) == (int64_t)UINT64_C(14695981039346656037));
    assert(spl_erased_key_hash(str("a")) != spl_erased_key_hash(str("b")));
    assert(spl_erased_key_hash(rt_value_int(42)) == 42);
    assert(spl_erased_key_hash(rt_value_int(-5)) == -5);
    assert(spl_erased_key_hash(17) == spl_erased_key_hash(17)); /* raw word */
    assert(spl_erased_key_hash(wide_low) == INT64_C(1152921504606846976));
    assert(spl_erased_key_hash(rt_value_u64(INT64_MAX)) == INT64_MAX);
    return 0;
}
