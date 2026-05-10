/* RISC-V Semihosting Interface */
#ifndef SEMIHOST_H
#define SEMIHOST_H

#include <stdint.h>
#include <stddef.h>

/* Semihosting operations */
#define SYS_OPEN    0x01
#define SYS_CLOSE   0x02
#define SYS_WRITEC  0x03
#define SYS_WRITE0  0x04
#define SYS_WRITE   0x05
#define SYS_READ    0x06
#define SYS_READC   0x07
#define SYS_CLOCK   0x10
#define SYS_EXIT    0x18

/* ADP constants */
#define ADP_Stopped_ApplicationExit 0x20026

/* Invoke semihosting call */
static inline long semihost_call(long op, long arg) {
    register long a0 __asm__("a0") = op;
    register long a1 __asm__("a1") = arg;
    __asm__ volatile (
        ".option push\n"
        ".option norvc\n"
        "slli zero, zero, 0x1f\n"
        "ebreak\n"
        "srai zero, zero, 0x7\n"
        ".option pop\n"
        : "+r"(a0)
        : "r"(a1)
        : "memory"
    );
    return a0;
}

/* Write a null-terminated string */
static inline void semihost_write0(const char *s) {
    semihost_call(SYS_WRITE0, (long)s);
}

/* Write a single character */
static inline void semihost_writec(char c) {
    semihost_call(SYS_WRITEC, (long)&c);
}

/* Exit with a status code */
static inline void semihost_exit(int code) {
    uint32_t params[2] = { ADP_Stopped_ApplicationExit, (uint32_t)code };
    semihost_call(SYS_EXIT, (long)params);
    /* Should not reach here */
    while(1) {}
}

/* Read system clock (centiseconds) */
static inline long semihost_clock(void) {
    return semihost_call(SYS_CLOCK, 0);
}

/* Simple integer to string (decimal) */
static inline void int_to_str(int val, char *buf, int bufsize) {
    if (bufsize < 2) return;
    if (val == 0) { buf[0] = '0'; buf[1] = '\0'; return; }
    int neg = 0;
    if (val < 0) { neg = 1; val = -val; }
    char tmp[12];
    int i = 0;
    while (val > 0 && i < 11) {
        tmp[i++] = '0' + (val % 10);
        val /= 10;
    }
    int j = 0;
    if (neg && j < bufsize - 1) buf[j++] = '-';
    while (i > 0 && j < bufsize - 1) buf[j++] = tmp[--i];
    buf[j] = '\0';
}

/* Print integer */
static inline void semihost_print_int(int val) {
    char buf[16];
    int_to_str(val, buf, sizeof(buf));
    semihost_write0(buf);
}

#endif /* SEMIHOST_H */
