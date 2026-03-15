/*
 * SimpleOS — L4 Microkernel Reference Implementation
 * common/compiler.h — Compiler attribute macros (clang / GCC)
 *
 * Compiled with: clang -O2 -ffreestanding -nostdlib
 */

#ifndef SIMPLE_OS_COMPILER_H
#define SIMPLE_OS_COMPILER_H

#define PACKED       __attribute__((packed))
#define ALIGNED(n)   __attribute__((aligned(n)))
#define NORETURN     __attribute__((noreturn))
#define INLINE       static inline __attribute__((always_inline))
#define SECTION(s)   __attribute__((section(s)))
#define UNUSED       __attribute__((unused))
#define LIKELY(x)    __builtin_expect(!!(x), 1)
#define UNLIKELY(x)  __builtin_expect(!!(x), 0)

#endif /* SIMPLE_OS_COMPILER_H */
