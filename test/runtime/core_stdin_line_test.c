/* Exercise the actual tagged-text provider through redirected process stdin. */
#include "runtime.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef _WIN32
#include <io.h>
#else
#include <unistd.h>
#endif

int main(int argc, char **argv) {
    int count = argc > 1 ? atoi(argv[1]) : 1;
    if (argc > 2 && strcmp(argv[2], "read-error") == 0) {
#ifdef _WIN32
        if (_close(_fileno(stdin)) != 0) return 91;
#else
        if (close(fileno(stdin)) != 0) return 91;
#endif
    }
    for (int i = 0; i < count; ++i) {
        int64_t value = rt_read_stdin_line();
        if (value == 0) {
            puts("nil");
            continue;
        }
        int64_t length = rt_string_len(value);
        const uint8_t *data = rt_string_data(value);
        if (length < 0 || (length && !data)) return 92;
        printf("text:%lld:", (long long)length);
        for (int64_t j = 0; j < length; ++j) printf("%02x", data[j]);
        putchar('\n');
    }
    return 0;
}
