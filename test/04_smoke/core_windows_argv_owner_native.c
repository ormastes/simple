/* Link with the real Windows standalone core runtime. No legacy array casts. */
#include "runtime.h"
#include <stdio.h>
#include <string.h>
extern SplArray *sys_get_args(void);

static int text_matches(int64_t word, const char *expected) {
    size_t length = strlen(expected);
    return rt_string_len(word) == (int64_t)length &&
        memcmp(rt_string_data(word), expected, length) == 0;
}

int main(void) {
    char *args[] = {"argv-owner.exe", "plain", "two words", "\xed\x95\x9c\xea\xb8\x80"};
    SplArray *(*providers[])(void) = {rt_cli_get_args, rt_get_args, sys_get_args};
    int checks = 0;
    spl_init_args(4, args);
    for (int provider = 0; provider < 3; provider++) {
        SplArray *array = providers[provider]();
        if (rt_array_len(array) != 4) return 10 + provider;
        checks++;
        for (int index = 0; index < 4; index++) {
            if (!text_matches(rt_array_get(array, index), args[index])) return 20 + provider;
            checks++;
        }
    }
    if (rt_cli_arg_count() != 4) return 30;
    checks++;
    for (int index = 0; index < 4; index++) {
        if (!text_matches(rt_cli_arg_at(index), args[index])) return 31;
        checks++;
    }
    if (!text_matches(rt_cli_arg_at(-1), "") || !text_matches(rt_cli_arg_at(4), "")) return 32;
    checks += 2;
    printf("CORE_WINDOWS_ARGV_OWNER_PASS checks=%d providers=3\n", checks);
    return 0;
}
