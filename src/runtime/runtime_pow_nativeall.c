/* Narrow native-all owner; the core runtime selects its intrinsic provider. */
#include "runtime_pow_private.h"

int64_t __simple_pow(int64_t base, int64_t exp) {
    return spl_runtime_integer_pow_v1(base, exp);
}
