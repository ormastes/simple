/* Link against the actual selected canonical core-C runtime archive.
 * Each negative mode runs in its own child; normal return is always failure.
 * Constants come from the canonical C/Rust RuntimeValue ABI header. */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include "../runtime_value.h"
typedef struct SplArray SplArray;
extern SplArray* rt_array_new(int64_t cap);
extern int8_t rt_array_push(SplArray* array, int64_t value);
extern int64_t rt_array_pop(SplArray* array);
extern int64_t rt_array_len(SplArray* array);
extern int64_t rt_unwrap_or_trap(int64_t value);
extern int64_t rt_option_some(int64_t payload);
extern int64_t rt_option_none(void);

static int present(void) {
    int64_t values[] = {0, (int64_t)RT_FALSE, (int64_t)RT_TRUE,
        (int64_t)RT_CHAR(0), (int64_t)RT_CHAR(0x37),
        (int64_t)RT_CHAR(0xE9), (int64_t)RT_CHAR(0x10FFFF)};
    unsigned checks = 0;
    for (unsigned i = 0; i < sizeof(values) / sizeof(values[0]); ++i) {
        int64_t expected = values[i];
        if (rt_unwrap_or_trap(expected) != expected) return 41;
        ++checks;
        SplArray* array = rt_array_new(1);
        if (!array || !rt_array_push(array, expected) || rt_array_len(array) != 1) return 42;
        int64_t popped = rt_array_pop(array);
        if (popped != expected || rt_array_len(array) != 0 || rt_unwrap_or_trap(popped) != expected) return 43;
        ++checks;
        if (rt_unwrap_or_trap(rt_option_some(expected)) != expected) return 44;
        ++checks;
    }
    if (checks != 21) return 45;
    puts("FLAT_UNWRAP_PRESENT_21_OK");
    return 0;
}

int main(int argc, char** argv) {
    if (argc != 2) return 64;
    if (strcmp(argv[1], "present") == 0) return present();
    int64_t absent;
    if (strcmp(argv[1], "nil") == 0) absent = (int64_t)RT_NIL;
    else if (strcmp(argv[1], "empty-pop") == 0) {
        SplArray* empty = rt_array_new(0);
        if (!empty || rt_array_len(empty) != 0) return 65;
        absent = rt_array_pop(empty);
        if (absent != (int64_t)RT_NIL) return 66;
    } else if (strcmp(argv[1], "boxed-none") == 0) absent = rt_option_none();
    else return 64;
    fprintf(stderr, "BEFORE_UNWRAP_%s\n", argv[1]);
    fflush(stderr);
    (void)rt_unwrap_or_trap(absent);
    fprintf(stderr, "UNEXPECTED_UNWRAP_RETURN_%s\n", argv[1]);
    return 67;
}
