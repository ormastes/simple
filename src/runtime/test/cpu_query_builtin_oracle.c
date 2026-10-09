/* Separate executable: its constructor must never enter the no-demand ELF. */
#include <stdio.h>
int main(void) {
    __builtin_cpu_init();
    unsigned features = !!__builtin_cpu_supports("sse") |
        (!!__builtin_cpu_supports("avx") << 1) |
        (!!__builtin_cpu_supports("avx2") << 2);
    printf("features=%u\n", features);
    return 0;
}
