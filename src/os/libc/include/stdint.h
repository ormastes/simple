/*
 * SimpleOS <stdint.h> — integer types
 *
 * Forward to the compiler's built-in header if available,
 * otherwise provide explicit definitions.
 */

#ifndef _SIMPLEOS_STDINT_H
#define _SIMPLEOS_STDINT_H

#if defined(__has_include) && __has_include_next(<stdint.h>)
#include_next <stdint.h>
#else

/* Exact-width signed */
typedef signed char        int8_t;
typedef short              int16_t;
typedef int                int32_t;
typedef long long          int64_t;

/* Exact-width unsigned */
typedef unsigned char      uint8_t;
typedef unsigned short     uint16_t;
typedef unsigned int       uint32_t;
typedef unsigned long long uint64_t;

/* Pointer-width types */
typedef long               intptr_t;
typedef unsigned long      uintptr_t;

/* Maximum-width types */
typedef long long          intmax_t;
typedef unsigned long long uintmax_t;

/* Minimum-width types */
typedef int8_t   int_least8_t;
typedef int16_t  int_least16_t;
typedef int32_t  int_least32_t;
typedef int64_t  int_least64_t;
typedef uint8_t  uint_least8_t;
typedef uint16_t uint_least16_t;
typedef uint32_t uint_least32_t;
typedef uint64_t uint_least64_t;

/* Fast types */
typedef int8_t   int_fast8_t;
typedef long     int_fast16_t;
typedef long     int_fast32_t;
typedef long     int_fast64_t;
typedef uint8_t  uint_fast8_t;
typedef unsigned long uint_fast16_t;
typedef unsigned long uint_fast32_t;
typedef unsigned long uint_fast64_t;

/* Limits */
#define INT8_MIN   (-128)
#define INT8_MAX   127
#define UINT8_MAX  255

#define INT16_MIN  (-32768)
#define INT16_MAX  32767
#define UINT16_MAX 65535

#define INT32_MIN  (-2147483647 - 1)
#define INT32_MAX  2147483647
#define UINT32_MAX 4294967295U

#define INT64_MIN  (-9223372036854775807LL - 1LL)
#define INT64_MAX  9223372036854775807LL
#define UINT64_MAX 18446744073709551615ULL

#define INTPTR_MIN  INT64_MIN
#define INTPTR_MAX  INT64_MAX
#define UINTPTR_MAX UINT64_MAX

#define INTMAX_MIN  INT64_MIN
#define INTMAX_MAX  INT64_MAX
#define UINTMAX_MAX UINT64_MAX

#define SIZE_MAX    UINTPTR_MAX
#define PTRDIFF_MIN INTPTR_MIN
#define PTRDIFF_MAX INTPTR_MAX

#endif /* __has_include_next */

#endif /* _SIMPLEOS_STDINT_H */
