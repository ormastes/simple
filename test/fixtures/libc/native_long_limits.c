/* Compile-only C ABI contract for SimpleOS compatibility limits.
 * Use the target Clang with -I src/os/libc/include -ffreestanding -nostdlib
 * -Werror=constant-conversion. This checks compiler-evaluated values and types,
 * independently of the textual definitions in the header.
 */
#include <limits.h>
#include <stddef.h>

_Static_assert(_Generic(SIZE_MAX, size_t: 1, default: 0),
               "SIZE_MAX must retain the target size_t type independently of long");
_Static_assert(SIZE_MAX == (size_t)~(size_t)0,
               "SIZE_MAX must cover every target size_t bit");

_Static_assert(_Generic(LONG_MAX, long: 1, default: 0),
               "LONG_MAX must have native signed-long type");
_Static_assert(_Generic(LONG_MIN, long: 1, default: 0),
               "LONG_MIN must have native signed-long type");
_Static_assert(_Generic(ULONG_MAX, unsigned long: 1, default: 0),
               "ULONG_MAX must have native unsigned-long type");
_Static_assert((unsigned long)LONG_MAX == (~0UL >> 1),
               "LONG_MAX must cover exactly the positive native-long range");
_Static_assert(ULONG_MAX == ~0UL,
               "ULONG_MAX must cover every unsigned-long bit");
_Static_assert(LONG_MIN + LONG_MAX == -1L,
               "native signed-long bounds must be complementary");
_Static_assert(LONG_MIN < 0L && LONG_MAX > 0L,
               "signed bounds must survive conversion to native long");

#if __SIZEOF_LONG__ == 4
_Static_assert(LONG_MAX == 2147483647L, "ILP32/LLP64 signed maximum");
_Static_assert(LONG_MIN == (-2147483647L - 1L), "ILP32/LLP64 signed minimum");
_Static_assert(ULONG_MAX == 4294967295UL, "ILP32/LLP64 unsigned maximum");
#elif __SIZEOF_LONG__ == 8
_Static_assert(LONG_MAX == 9223372036854775807L, "LP64 signed maximum");
_Static_assert(LONG_MIN == (-9223372036854775807L - 1L), "LP64 signed minimum");
_Static_assert(ULONG_MAX == 18446744073709551615UL, "LP64 unsigned maximum");
#else
#error "Unsupported native-long ABI in SimpleOS limit contract"
#endif

/* Match the native return types used by strtol/strtoul overflow handling. */
long simpleos_limits_test_signed_clamp(int negative) {
    return negative ? LONG_MIN : LONG_MAX;
}

unsigned long simpleos_limits_test_unsigned_clamp(void) {
    return ULONG_MAX;
}
