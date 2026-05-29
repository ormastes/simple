#ifndef MAILBOX_H
#define MAILBOX_H

#include <stdint.h>

#define MB_BASE     0x80FF0000UL
#define MB_CMD      (*(volatile uint32_t*)(MB_BASE + 0x00))
#define MB_ARG0     (*(volatile uint32_t*)(MB_BASE + 0x04))
#define MB_ARG1     (*(volatile uint32_t*)(MB_BASE + 0x08))
#define MB_STATUS   (*(volatile uint32_t*)(MB_BASE + 0x0C))
#define MB_RESULT   (*(volatile uint32_t*)(MB_BASE + 0x10))
#define MB_SEQ_ID   (*(volatile uint32_t*)(MB_BASE + 0x14))
#define MB_TRIGGER  (*(volatile uint32_t*)(MB_BASE + 0x18))

#define CMD_PUTC    0x01
#define CMD_EXIT    0x02
#define CMD_RESULT  0x03

#define TRIGGER_MAGIC 0x0000DEAD

static uint32_t mb_seq = 0;

static inline void mb_putc(char c) {
    MB_CMD  = CMD_PUTC;
    MB_ARG0 = (uint32_t)c;
    MB_SEQ_ID = ++mb_seq;
    MB_TRIGGER = TRIGGER_MAGIC;
}

static inline void mb_puts(const char *s) {
    while (*s) { mb_putc(*s++); }
}

static inline void mb_exit(uint32_t code) {
    MB_CMD  = CMD_EXIT;
    MB_ARG0 = code;
    MB_SEQ_ID = ++mb_seq;
    MB_TRIGGER = TRIGGER_MAGIC;
    while (1) {} /* halt */
}

static inline void mb_result(uint32_t pass, uint32_t value) {
    MB_CMD  = CMD_RESULT;
    MB_ARG0 = pass;
    MB_ARG1 = value;
    MB_SEQ_ID = ++mb_seq;
    MB_TRIGGER = TRIGGER_MAGIC;
}

#endif
