/*
 * SimpleOS <setjmp.h> — non-local jumps
 */

#ifndef _SIMPLEOS_SETJMP_H
#define _SIMPLEOS_SETJMP_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* jmp_buf stores callee-saved registers + stack pointer + return address */
typedef uint64_t jmp_buf[8];

int  setjmp(jmp_buf env);
void longjmp(jmp_buf env, int val) __attribute__((noreturn));

int  _setjmp(jmp_buf env);
void _longjmp(jmp_buf env, int val) __attribute__((noreturn));

#ifdef __cplusplus
}
#endif

#endif /* _SIMPLEOS_SETJMP_H */
