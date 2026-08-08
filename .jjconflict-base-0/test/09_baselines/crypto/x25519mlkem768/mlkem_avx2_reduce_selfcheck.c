#include <stdint.h>
#include <stdio.h>

#include "runtime.h"

int main(void) {
    int64_t result = rt_mlkem_modq_avx2_selfcheck();
    if (result < 0) {
        puts("MLKEM_AVX2_REDUCE_SELFCHECK: UNAVAILABLE");
        return 77;
    }
    printf("mlkem_avx2_reduce_mismatches=%lld\n", (long long)result);
    if (result != 0) return 1;
    puts("MLKEM_AVX2_REDUCE_SELFCHECK: PASS");
    return 0;
}
