#include "runtime.h"
#include <stdio.h>
#include <string.h>

int main(void) {
    int failures = 0;
    for (int64_t cap = 0; cap <= 3; cap += 3) {
        const char* script = "printf xyz >&2; exit 127";
        SplArray* args = rt_array_new(2);
        rt_array_push(args, rt_string_new((const uint8_t*)"-c", 2));
        rt_array_push(args, rt_string_new((const uint8_t*)script, strlen(script)));
        int64_t result = rt_process_run_bounded_bytes("/bin/sh", 7, args, 1000, cap);
        int64_t err = rt_tuple_get(result, 1);
        if (rt_value_as_int(rt_tuple_get(result, 2)) != 127 || rt_array_len((SplArray*)(uintptr_t)err) != cap) ++failures;
        if (cap == 3 && rt_value_as_int(rt_array_get((SplArray*)(uintptr_t)err, 2)) != 'z') ++failures;
        rt_array_free(args);
    }
    printf("POSIX raw exit127 cap0/cap3: %d failures\n", failures);
    return failures;
}
