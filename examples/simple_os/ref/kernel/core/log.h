/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/log.h -- Kernel debug logging over UART serial
 *
 * Mirrors: spl/kernel/core/log.spl
 *
 * Log levels follow severity ordering:
 *   Debug < Info < Warn < Error < Panic
 */

#ifndef SIMPLE_OS_LOG_H
#define SIMPLE_OS_LOG_H

#include "common/types.h"
#include "common/compiler.h"

/* ---- Log levels -------------------------------------------------------- */

typedef enum {
    LOG_LEVEL_DEBUG = 0,
    LOG_LEVEL_INFO  = 1,
    LOG_LEVEL_WARN  = 2,
    LOG_LEVEL_ERROR = 3,
    LOG_LEVEL_PANIC = 4,
} log_level_t;

/* ---- API --------------------------------------------------------------- */

/* Initialize the logging subsystem (sets up UART). */
void klog_init(void);

/* Set the minimum log level. Messages below are discarded. */
void klog_set_level(log_level_t level);

/* Core log function: prints "[LEVEL] msg\n" */
void klog(log_level_t level, const char *msg);

/* Convenience wrappers */
void klog_debug(const char *msg);
void klog_info(const char *msg);
void klog_warn(const char *msg);
void klog_error(const char *msg);

/* Log with a hex value appended: "[LEVEL] msg 0xXXXXXXXX\n" */
void klog_hex(log_level_t level, const char *msg, uint32_t value);

/* Log with a decimal value appended: "[LEVEL] msg N\n" */
void klog_dec(log_level_t level, const char *msg, uint32_t value);

/* Kernel panic: print message and halt. Never returns. */
NORETURN void kpanic(const char *msg);

#endif /* SIMPLE_OS_LOG_H */
