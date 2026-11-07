#ifndef SIMPLEOS_FREESTANDING_BOOL_ABI_H
#define SIMPLEOS_FREESTANDING_BOOL_ABI_H

#include <stdint.h>

/* Tagged RuntimeValue booleans, distinct from unboxed C/MIR bools (0/1)
 * and encoded integers (0/8).  TAG_SPECIAL=3, payload true=1/false=2. */
#define SIMPLEOS_TAGGED_BOOL_TRUE  11ULL
#define SIMPLEOS_TAGGED_BOOL_FALSE 19ULL

/* Preserve the logical helpers' encoded-integer truthiness while recognizing
 * both tagged booleans.  Only zero/nonzero of the decoded integer matters:
 * unsigned shifting gives the same answer for negative values without relying
 * on implementation-defined signed right shift. */
static inline int simpleos_bool_or_integer_truthy(uint64_t value)
{
    if (value == SIMPLEOS_TAGGED_BOOL_TRUE) return 1;
    if (value == SIMPLEOS_TAGGED_BOOL_FALSE) return 0;
    return (value >> 3) != 0;
}

#endif
