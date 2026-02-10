/*
 * Simple Seed — Common CRT Logic
 *
 * Shared startup/shutdown sequence used by all platforms.
 * Platform ASM extracts argc/argv/envp and calls __spl_start().
 */

#include "crt_common.h"

/* Run init_array constructors */
static void run_init(void) {
    int64_t count = __init_array_end - __init_array_start;
    for (int64_t i = 0; i < count; i++) {
        if (__init_array_start[i]) {
            __init_array_start[i]();
        }
    }
}

/* Run fini_array destructors */
static void run_fini(void) {
    int64_t count = __fini_array_end - __fini_array_start;
    for (int64_t i = count - 1; i >= 0; i--) {
        if (__fini_array_start[i]) {
            __fini_array_start[i]();
        }
    }
}

/* Zero BSS section (baremetal only; hosted OS does this) */
void __spl_zero_bss(void) {
    for (char *p = __bss_start; p < __bss_end; p++) {
        *p = 0;
    }
}

/*
 * Common startup entry point.
 * Called by platform-specific ASM after setting up argc/argv/envp.
 */
void __spl_start(int argc, char **argv, char **envp) {
    (void)envp; /* available for future use */

    run_init();
    spl_init_args(argc, argv);

    int status = main(argc, argv);

    run_fini();
    __spl_exit(status);
}
