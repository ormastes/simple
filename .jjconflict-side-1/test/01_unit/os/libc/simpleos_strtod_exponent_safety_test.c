typedef int wchar_t;
int errno = 0;

#define strtod simpleos_test_strtod
#define strtof simpleos_test_strtof
#include "src/os/libc/simpleos_stdlib_ext.c"

int main(void) {
    char *end = 0;
    double value;

    errno = 0;
    value = simpleos_test_strtod("1e999999999999", &end);
    if (*end != '\0' || errno != ERANGE || value != __builtin_huge_val()) return 1;

    errno = 0;
    value = simpleos_test_strtod("1e-999999999999", &end);
    if (*end != '\0' || errno != ERANGE || value != 0.0) return 2;

    errno = 0;
    value = simpleos_test_strtod("0e999999999999", &end);
    if (*end != '\0' || errno != 0 || value != 0.0) return 3;

    errno = 0;
    value = simpleos_test_strtod("1.25e2", &end);
    if (*end != '\0' || errno != 0 || value != 125.0) return 4;

    return 0;
}
