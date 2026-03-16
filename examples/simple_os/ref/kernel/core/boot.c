/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/boot.c -- kernel_main entry point
 *
 * Initializes all kernel subsystems and starts the scheduler.
 *
 * Boot sequence:
 *   1. Init UART serial (for klog output)
 *   2. Print [BOOT OK]
 *   3. Init GDT, IDT, PIC, PIT   (stubbed)
 *   4. Init frame allocator       (stubbed)
 *   5. Init paging                (stubbed)
 *   6. Create root task            (stubbed)
 *   7. Start scheduler            (stubbed)
 *   8. Halt (should never reach)
 */

#include "kernel/core/boot.h"
#include "kernel/core/log.h"

/* ---- External arch init stubs (provided by arch layer) ----------------- */

/* These are declared but not yet implemented.  Each init function
 * will be filled in when the corresponding arch module is written. */

extern void gdt_init(void);
extern void idt_init(void);
extern void pic_init(void);
extern void pit_init(uint32_t freq_hz);
extern void frame_alloc_init(uint32_t mem_start, uint32_t mem_end);
extern void paging_init(void);

/* ---- Boot -------------------------------------------------------------- */

NORETURN void kernel_main(void)
{
    /* 1. Initialize logging (sets up UART serial) */
    klog_init();

    /* 2. Announce boot */
    klog_info("[BOOT OK]");

    /* 3. Initialize CPU tables and interrupt controller */
    /* gdt_init(); */
    /* idt_init(); */
    /* pic_init(); */
    /* pit_init(TICK_FREQ_HZ); */

    /* 4. Initialize physical memory allocator */
    /* frame_alloc_init(0x00100000, 0x04000000); */

    /* 5. Initialize virtual memory / paging */
    /* paging_init(); */

    /* 6. Create the root task (first user-space thread) */
    /* TODO: create root task TCB, CSpace, VSpace, IPC buffer */

    /* 7. Start the scheduler */
    /* TODO: scheduler_init + scheduler_schedule */

    /* 8. Should never reach here */
    klog_info("[BOOT] Init complete, entering idle loop");

    /* Halt loop (architecture-specific wait-for-interrupt) */
    for (;;) {
#if defined(__i386__) || defined(__x86_64__)
        __asm__ volatile ("hlt");
#elif defined(__aarch64__) || defined(__arm__)
        __asm__ volatile ("wfi");
#elif defined(__riscv)
        __asm__ volatile ("wfi");
#else
        /* Busy-wait fallback */
        ;
#endif
    }
}
