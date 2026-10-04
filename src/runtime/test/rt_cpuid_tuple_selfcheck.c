/* Exercise the real runtime tuple boundary, including signed register bits. */
#include <stdint.h>
#include <stdio.h>

typedef struct { int32_t a, b, c, d; } RtCpuidResult;
extern RtCpuidResult rt_cpuid(int32_t leaf, int32_t subleaf);
extern int64_t rt_cpuid_tuple(int32_t leaf, int32_t subleaf);
extern int64_t rt_tuple_len(int64_t tuple);
extern int64_t rt_tuple_get(int64_t tuple, int64_t index);
extern int64_t rt_value_as_int(int64_t value);

int main(void) {
    /* Vendor/max-leaf registers are stable across scheduler migration. */
    const int32_t leaves[] = {0, (int32_t)UINT32_C(0x80000000)};
    for (unsigned n = 0; n < sizeof(leaves) / sizeof(leaves[0]); ++n) {
        RtCpuidResult raw = rt_cpuid(leaves[n], 0);
        const int32_t expected[] = {raw.a, raw.b, raw.c, raw.d};
        int64_t tuple = rt_cpuid_tuple(leaves[n], 0);
        if (rt_tuple_len(tuple) != 4) return 1;
        for (int64_t i = 0; i < 4; ++i) {
            if (rt_value_as_int(rt_tuple_get(tuple, i)) != expected[i]) {
                fprintf(stderr, "CPUID tuple mismatch: leaf=%u register=%lld\n",
                        (unsigned)leaves[n], (long long)i);
                return 2;
            }
        }
    }
    puts("PASS: CPUID tuple preserves four signed registers");
    return 0;
}
