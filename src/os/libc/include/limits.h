/*
 * SimpleOS <limits.h> — implementation-defined limits
 */

#ifndef _SIMPLEOS_LIMITS_H
#define _SIMPLEOS_LIMITS_H

#define CHAR_BIT   8

#define SCHAR_MIN  (-128)
#define SCHAR_MAX  127
#define UCHAR_MAX  255

#define CHAR_MIN   SCHAR_MIN
#define CHAR_MAX   SCHAR_MAX

#define SHRT_MIN   (-32768)
#define SHRT_MAX   32767
#define USHRT_MAX  65535

#define INT_MIN    (-2147483647 - 1)
#define INT_MAX    2147483647
#define UINT_MAX   4294967295U

/* `long` follows the target C ABI, not the compiler host or the Simple i64
 * value representation. Clang supplies a correctly typed native-long limit
 * for ILP32, LP64 and LLP64; deriving the other bounds avoids narrowing. */
#define LONG_MAX   __LONG_MAX__
#define LONG_MIN   (-LONG_MAX - 1L)
#define ULONG_MAX  (2UL * LONG_MAX + 1UL)

#define LLONG_MIN  (-9223372036854775807LL - 1LL)
#define LLONG_MAX  9223372036854775807LL
#define ULLONG_MAX 18446744073709551615ULL

#define PATH_MAX   4096
#define NAME_MAX   255
#define PIPE_BUF   4096
#define PAGESIZE   4096

#define SSIZE_MAX  LONG_MAX
#ifndef SIZE_MAX
/* size_t can be wider than unsigned long under LLP64. */
#define SIZE_MAX   __SIZE_MAX__
#endif

#endif /* _SIMPLEOS_LIMITS_H */
