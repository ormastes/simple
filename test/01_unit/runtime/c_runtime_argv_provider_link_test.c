#include "runtime.h"

#include <assert.h>
#include <stdint.h>
#include <string.h>

extern SplArray *sys_get_args(void);

static void assert_array_arg(SplArray *array, int64_t index, const char *expected) {
    const int64_t value = rt_array_get(array, index);
    const int64_t length = rt_string_len(value);
    assert(length == (int64_t)strlen(expected));
    assert(memcmp(rt_string_data(value), expected, (size_t)length) == 0);
}

int main(void) {
    char arg0[] = "simple";
    char arg1[] = "check";
    char arg2[] = "module.spl";
    char *argv[] = {arg0, arg1, arg2};

    rt_set_args(3, argv);
    assert(spl_arg_count() == 3);
    assert(rt_get_argc() == 3);
    assert(rt_cli_arg_count() == 3);
    assert(strcmp(spl_get_arg(1), "check") == 0);
    assert(strcmp(spl_get_arg(-1), "") == 0);
    assert(strcmp(spl_get_arg(3), "") == 0);

    SplArray *cli_args = rt_cli_get_args();
    SplArray *get_args = rt_get_args();
    SplArray *sys_args = sys_get_args();
    assert(rt_array_len(cli_args) == 3);
    assert(rt_array_len(get_args) == 3);
    assert(rt_array_len(sys_args) == 3);
    assert_array_arg(cli_args, 1, "check");
    assert_array_arg(get_args, 1, "check");
    assert_array_arg(sys_args, 1, "check");

    /* C owns the filtered pointer vector, borrows bytes, and copies value text. */
    arg1[0] = 'C';
    assert(strcmp(spl_get_arg(1), "Check") == 0);
    assert_array_arg(cli_args, 1, "check");
    assert_array_arg(get_args, 1, "check");
    assert_array_arg(sys_args, 1, "check");

    const int64_t direct = rt_cli_arg_at(1);
    assert(rt_string_len(direct) == 5);
    assert(memcmp(rt_string_data(direct), "Check", 5) == 0);
    assert(rt_string_len(rt_cli_arg_at(-1)) == 0);
    assert(rt_string_len(rt_cli_arg_at(3)) == 0);
    return 0;
}
