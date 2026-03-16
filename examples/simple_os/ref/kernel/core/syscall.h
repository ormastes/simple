/*
 * SimpleOS — L4 Microkernel Reference Implementation
 * kernel/core/syscall.h — System call dispatch interface
 *
 * Called from arch-specific syscall entry assembly.
 */

#ifndef SIMPLE_OS_SYSCALL_H
#define SIMPLE_OS_SYSCALL_H

#include "common/types.h"

/*
 * Dispatch a system call.
 *
 * Parameters:
 *   num  — syscall number
 *   a0–a4 — up to 5 arguments passed from user space
 *
 * Returns: syscall result value (placed in eax by assembly stub).
 */
uint32_t syscall_dispatch(uint32_t num, uint32_t a0, uint32_t a1,
                          uint32_t a2, uint32_t a3, uint32_t a4);

#endif /* SIMPLE_OS_SYSCALL_H */
