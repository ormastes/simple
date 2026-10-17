#include <stdint.h>

extern int64_t rt_value_int(int64_t);
extern int64_t rt_value_bool(int64_t);
extern int64_t rt_value_nil(void);
extern int64_t rt_string_new(const uint8_t *, uint64_t);
extern void rt_value_print(int64_t);
extern void rt_value_println(int64_t);
extern void rt_print(const char *);
extern void rt_println(const char *);

/* Link with the selected C objects AND native-all. These constructors belong
 * to the selected C tagged-value provider; Rust heap interchange is separate.
 * Exact stdout is the oracle, including nil's empty body and raw C pointers. */
int main(void) {
    rt_print("raw:");
    rt_println("pointer");
    rt_value_print(rt_value_nil());
    rt_value_println(rt_value_nil());
    rt_value_print(rt_value_int(42));
    rt_value_println(rt_value_int(-7));
    rt_value_print(rt_value_bool(1));
    rt_value_println(rt_value_bool(0));
    rt_value_print(rt_string_new((const uint8_t *)"tagged:", 7));
    rt_value_println(rt_string_new((const uint8_t *)"value", 5));
    return 0;
}
