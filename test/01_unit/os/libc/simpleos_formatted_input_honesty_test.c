#include <stdint.h>

int simpleos_test_errno = 0;
#define errno simpleos_test_errno

int64_t simpleos_syscall(int64_t id, int64_t a0, int64_t a1, int64_t a2,
                         int64_t a3, int64_t a4) {
    (void)id; (void)a0; (void)a1; (void)a2; (void)a3; (void)a4;
    return -38;
}

#define scanf simpleos_test_scanf
#define fscanf simpleos_test_fscanf
#define sscanf simpleos_test_sscanf
#define vsscanf simpleos_test_vsscanf
#include "src/os/libc/simpleos_libc_ext.c"

int main(void) {
    int value = 0;
    simpleos_test_errno = 0;
    if (simpleos_test_sscanf("12", "%d", &value) != EOF || simpleos_test_errno != ENOSYS) return 1;
    simpleos_test_errno = 0;
    if (simpleos_test_scanf("%d", &value) != EOF || simpleos_test_errno != ENOSYS) return 2;
    simpleos_test_errno = 0;
    if (simpleos_test_fscanf(NULL, "%d", &value) != EOF || simpleos_test_errno != ENOSYS) return 3;
    return 0;
}
