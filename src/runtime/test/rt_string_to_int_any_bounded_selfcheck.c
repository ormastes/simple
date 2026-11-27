/* Regression: rt_string_to_int_any must honour the tagged string length and
 * never parse bytes past s->len (bug native_int_text_unbounded_strtoll_2026_11_03,
 * root of phase2_octal_permission_mode_lowering_2026_10_27). */
#include <stdint.h>
#include <stdio.h>

extern int64_t rt_string_new(const uint8_t* bytes, uint64_t len);
extern int64_t rt_string_to_int_any(int64_t value);

int main(void) {
    const uint8_t buf[] = "600";
    int fails = 0;
    if (rt_string_to_int_any(rt_string_new(buf, 1)) != 6) { puts("FAIL len1"); fails++; }
    if (rt_string_to_int_any(rt_string_new(buf, 2)) != 60) { puts("FAIL len2"); fails++; }
    if (rt_string_to_int_any(rt_string_new(buf, 3)) != 600) { puts("FAIL len3"); fails++; }
    if (rt_string_to_int_any((int64_t)(uintptr_t)"42") != 42) { puts("FAIL raw"); fails++; }
    if (!fails) puts("PASS rt_string_to_int_any bounded");
    return fails ? 1 : 0;
}
