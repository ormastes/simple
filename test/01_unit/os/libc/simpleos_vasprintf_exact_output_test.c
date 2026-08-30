#include <stdarg.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

int simpleos_test_errno = 0;
#define errno simpleos_test_errno

int64_t simpleos_syscall(int64_t id, int64_t a0, int64_t a1, int64_t a2,
                         int64_t a3, int64_t a4) {
    (void)id; (void)a0; (void)a1; (void)a2; (void)a3; (void)a4;
    return -38;
}

#define vasprintf simpleos_test_vasprintf
#include "src/os/libc/simpleos_libc_ext.c"

static int test_asprintf(char **output, const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    int result = simpleos_test_vasprintf(output, fmt, ap);
    va_end(ap);
    return result;
}

int main(void) {
    char *small = NULL;
    if (test_asprintf(&small, "%s:%d", "audit", 7) != 7) return 1;
    if (!small || strcmp(small, "audit:7") != 0) return 2;
    free(small);

    char payload[5001];
    for (int i = 0; i < 5000; ++i) payload[i] = 'x';
    payload[5000] = '\0';
    char *large = NULL;
    if (test_asprintf(&large, "prefix-%s-suffix", payload) != 5014) return 3;
    if (!large || strlen(large) != 5014) return 4;
    if (strncmp(large, "prefix-", 7) != 0) return 5;
    if (strcmp(large + 5007, "-suffix") != 0) return 6;
    free(large);

    simpleos_test_errno = 0;
    if (test_asprintf(NULL, "%s", "x") != -1 || simpleos_test_errno != EINVAL) return 7;
    return 0;
}
