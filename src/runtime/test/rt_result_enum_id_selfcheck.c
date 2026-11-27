/* #6953: Ok/Err may only be read under a real Result enum id (0 compiled, 2
 * from rt_result_ok/err). A user enum's declared index is 0/1 for its first
 * two variants, so an erased `?` (expected id 0, Err index 1) must not treat
 * it as Err, and the Result readers must accept the C id 2.
 * Build like check_enum_mixed_owner.sh: runtime runtime_native runtime_memory
 * runtime_memtrack objects + this file, -Wl,--allow-multiple-definition. */
#include <stdio.h>
#include <stdint.h>
#include "../runtime_value.h"
extern int64_t rt_enum_new(int32_t enum_id, int32_t discriminant, int64_t payload);
extern int8_t rt_try_is_absent(int64_t value, int64_t expected_enum_id, int64_t err_discriminant);
extern int64_t rt_unwrap_or_value(int64_t value, int64_t default_val);
extern int8_t rt_is_present(int64_t value);
extern int64_t rt_option_map(int64_t value, int64_t closure_value);
extern int64_t rt_result_ok(int64_t payload);
extern int64_t rt_result_err(int64_t payload);

#define INT(v) ((int64_t)(v) << 3)

int main(void) {
    int64_t user = rt_enum_new(851885673, 1, INT(40));
    if (rt_try_is_absent(user, 0, 1)) return 11;
    int32_t ids[] = {0, 2};
    for (unsigned i = 0; i < 2; ++i) {
        if (!rt_try_is_absent(rt_enum_new(ids[i], 1, INT(0)), 0, 1)) return 12;
        if (rt_try_is_absent(rt_enum_new(ids[i], 0, INT(0)), 0, 1)) return 13;
    }
    int64_t err = rt_result_err(INT(9));
    int64_t ok = rt_result_ok(INT(42));
    if (rt_unwrap_or_value(err, INT(7)) != INT(7)) return 21;
    if (rt_unwrap_or_value(ok, INT(7)) != INT(42)) return 22;
    if (rt_is_present(err)) return 23;
    if (rt_option_map(err, 0) != err) return 24;
    puts("rt_result_enum_id_selfcheck: PASS");
    return 0;
}
