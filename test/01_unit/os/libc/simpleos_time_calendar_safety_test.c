#include <stdint.h>

int simpleos_test_errno = 0;
#define errno simpleos_test_errno

int64_t simpleos_syscall(int64_t number, int64_t a, int64_t b, int64_t c,
                         int64_t d, int64_t e) {
    (void)number; (void)a; (void)b; (void)c; (void)d; (void)e;
    return 0;
}

#define gmtime simpleos_test_gmtime
#define localtime simpleos_test_localtime
#define mktime simpleos_test_mktime
#define strftime simpleos_test_strftime
#include "src/os/libc/simpleos_time.c"

int main(void) {
    char output[64];
    time_t epoch = 0;
    struct tm valid = {
        .tm_sec = 0, .tm_min = 0, .tm_hour = 0, .tm_mday = 1,
        .tm_mon = 0, .tm_year = 70
    };
    if (simpleos_test_gmtime(NULL) != NULL || simpleos_test_errno != EFAULT) return 1;
    simpleos_test_errno = 0;
    epoch = -1;
    if (simpleos_test_gmtime(&epoch) != NULL || simpleos_test_errno != ERANGE) return 2;
    if (simpleos_test_mktime(NULL) != (time_t)-1 || simpleos_test_errno != EFAULT) return 3;
    simpleos_test_errno = 0;
    valid.tm_mon = 12;
    if (simpleos_test_mktime(&valid) == (time_t)-1 || valid.tm_year != 125 || valid.tm_mon != 0 || valid.tm_mday != 1) return 4;
    valid.tm_year = 70;
    valid.tm_mon = 0;
    if (simpleos_test_strftime(NULL, sizeof(output), "%Y", &valid) != 0 || simpleos_test_errno != EFAULT) return 5;
    simpleos_test_errno = 0;
    valid.tm_mday = 32;
    if (simpleos_test_strftime(output, sizeof(output), "%Y", &valid) != 0 || simpleos_test_errno != EINVAL) return 6;
    valid.tm_mday = 1;
    if (simpleos_test_strftime(output, sizeof(output), "%Y-%m-%d", &valid) != 10) return 7;
    if (output[0] != '1' || output[1] != '9' || output[2] != '7' ||
        output[3] != '0' || output[4] != '-' || output[9] != '1' ||
        output[10] != '\0') return 8;
    return 0;
}
