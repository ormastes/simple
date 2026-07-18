/*
 * SimpleOS <setjmp.h> — non-local jumps
 */

#ifndef _SIMPLEOS_SETJMP_H
#define _SIMPLEOS_SETJMP_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* jmp_buf stores the platform callee-saved state used by setjmp.S. */
#if defined(__aarch64__)
/* x19-x28, x29, x30, sp, d8-d15 (see simpleos_setjmp_aarch64.S) */
typedef uint64_t jmp_buf[24];
#else
typedef uint64_t jmp_buf[16];
#endif

int  setjmp(jmp_buf env);
void longjmp(jmp_buf env, int val) __attribute__((noreturn));

int  _setjmp(jmp_buf env);
void _longjmp(jmp_buf env, int val) __attribute__((noreturn));

#ifdef __cplusplus
}
#endif

#endif /* _SIMPLEOS_SETJMP_H */
