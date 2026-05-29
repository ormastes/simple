#include "runtime_value.h"

extern RuntimeValue rt_array_new(uint64_t capacity);
extern void rt_array_push(RuntimeValue arr, RuntimeValue val);

RuntimeValue sffi_regex_is_match(RuntimeValue pattern, RuntimeValue text) {
    (void)pattern; (void)text;
    return RT_FALSE;
}

RuntimeValue sffi_regex_find(RuntimeValue pattern, RuntimeValue text) {
    (void)pattern; (void)text;
    return rt_array_new(0);
}

RuntimeValue sffi_regex_find_all(RuntimeValue pattern, RuntimeValue text) {
    (void)pattern; (void)text;
    return rt_array_new(0);
}

RuntimeValue sffi_regex_captures(RuntimeValue pattern, RuntimeValue text) {
    (void)pattern; (void)text;
    return rt_array_new(0);
}

RuntimeValue sffi_regex_replace(RuntimeValue pattern, RuntimeValue text, RuntimeValue replacement) {
    (void)pattern; (void)replacement;
    return text;
}

RuntimeValue sffi_regex_replace_all(RuntimeValue pattern, RuntimeValue text, RuntimeValue replacement) {
    (void)pattern; (void)replacement;
    return text;
}

RuntimeValue sffi_regex_split(RuntimeValue pattern, RuntimeValue text) {
    (void)pattern;
    RuntimeValue result = rt_array_new(1);
    rt_array_push(result, text);
    return result;
}

RuntimeValue sffi_regex_split_n(RuntimeValue pattern, RuntimeValue text, RuntimeValue limit) {
    (void)pattern; (void)limit;
    RuntimeValue result = rt_array_new(1);
    rt_array_push(result, text);
    return result;
}
