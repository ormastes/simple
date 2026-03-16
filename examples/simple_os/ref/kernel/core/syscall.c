/*
 * SimpleOS — L4 Microkernel Reference Implementation
 * kernel/core/syscall.c — System call dispatch stub
 *
 * Called from arch/x86/trap/syscall_entry.S.
 * TODO: implement actual syscall routing.
 */

#include "kernel/core/syscall.h"

uint32_t syscall_dispatch(uint32_t num, uint32_t a0, uint32_t a1,
                          uint32_t a2, uint32_t a3, uint32_t a4)
{
    (void)num;
    (void)a0;
    (void)a1;
    (void)a2;
    (void)a3;
    (void)a4;

    return 0; /* TODO: implement */
}
