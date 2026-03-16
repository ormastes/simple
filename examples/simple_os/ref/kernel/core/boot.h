/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/boot.h -- kernel_main entry point
 *
 * Called from the multiboot assembly stub after basic hardware is set up.
 */

#ifndef SIMPLE_OS_BOOT_H
#define SIMPLE_OS_BOOT_H

#include "common/types.h"
#include "common/compiler.h"

/* Kernel entry point.  Called by the bootloader / multiboot stub.
 * Initializes all subsystems and starts the scheduler.
 * Never returns. */
NORETURN void kernel_main(void);

#endif /* SIMPLE_OS_BOOT_H */
