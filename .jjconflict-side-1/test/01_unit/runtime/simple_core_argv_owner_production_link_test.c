#include "runtime.h"

#include <assert.h>
#include <stdint.h>
#include <string.h>

/*
 * Deliberately win the duplicate public-array symbols.  The selected
 * pure-Simple argv bridge must use its private owner helpers and never call
 * either poison body, even with the production allow-multiple-definition
 * policy.
 */
static int poison_new_calls;
static int poison_push_calls;

SplArray *rt_array_new(int64_t capacity) {
    (void)capacity;
    poison_new_calls++;
    return NULL;
}

int8_t rt_array_push(SplArray *array, int64_t value) {
    (void)array;
    (void)value;
    poison_push_calls++;
    return 0;
}

extern int64_t array_is_valid(int64_t array);
extern int64_t array_len_value(int64_t array);
extern int64_t array_get_raw(int64_t array, int64_t index);
extern SplArray *sys_get_args(void);

int main(void) {
    char arg0[] = "simple";
    char arg1[] = "build";
    char arg2[] = "bootstrap";
    char *argv[] = {arg0, arg1, arg2};

    rt_set_args(3, argv);
    const int64_t args = (int64_t)(uintptr_t)rt_cli_get_args();

    assert(spl_arg_count() == 3);
    assert(rt_get_argc() == 3);
    assert(rt_cli_arg_count() == 3);
    assert(strcmp(spl_get_arg(1), "build") == 0);
    assert(args > 4095);
    assert(array_is_valid(args) == 1);
    assert(array_len_value(args) == 3);
    assert(poison_new_calls == 0);
    assert(poison_push_calls == 0);

    static const char *const expected[] = {"simple", "build", "bootstrap"};
    for (int64_t i = 0; i < 3; ++i) {
        const int64_t value = array_get_raw(args, i);
        const int64_t length = rt_string_len(value);
        const uint8_t *data = rt_string_data(value);
        assert(length == (int64_t)strlen(expected[i]));
        assert(data != NULL);
        assert(memcmp(data, expected[i], (size_t)length) == 0);

        const int64_t direct = rt_cli_arg_at(i);
        assert(rt_string_len(direct) == length);
        assert(memcmp(rt_string_data(direct), expected[i], (size_t)length) == 0);
    }

    assert((int64_t)(uintptr_t)rt_get_args() == args ||
           array_len_value((int64_t)(uintptr_t)rt_get_args()) == 3);
    assert(array_len_value((int64_t)(uintptr_t)sys_get_args()) == 3);
    return 0;
}
