/*
 * SimpleOS RV32 minimal startup/stdout capsule.
 *
 * Policy stays in pure Simple; this file owns only 16550 UART writes,
 * stdout/stderr ABI hooks, stack handoff to spl_start, and WFI halt.
 */

#include <stdint.h>
#include <stddef.h>

typedef intptr_t RuntimeValue;

#define TAG_MASK    ((uintptr_t)0x7)
#define TAG_INT     ((uintptr_t)0x0)
#define TAG_HEAP    ((uintptr_t)0x1)
#define ENCODE_INT(v) ((RuntimeValue)(((uint32_t)(int32_t)(v) << 3) | TAG_INT))
#define DECODE_PTR(v) ((void *)((uintptr_t)(v) & ~TAG_MASK))
#define IS_HEAP(v)    (((uintptr_t)(v) & TAG_MASK) == TAG_HEAP)
#define HEAP_STRING 1u

typedef struct {
    uint32_t type;
    uint32_t size;
} HeapHeader;

typedef struct {
    HeapHeader hdr;
    uint32_t len;
    char data[];
} RuntimeString;

#define UART_BASE 0x10000000UL
#define UART_THR 0x00UL
#define UART_LSR 0x05UL
#define UART_LSR_THRE 0x20u

void serial_putchar(char c)
{
    volatile uint8_t *uart = (volatile uint8_t *)UART_BASE;
    for (uint32_t spin = 0; spin < 100000u; spin++) {
        if ((uart[UART_LSR] & UART_LSR_THRE) != 0u) break;
    }
    uart[UART_THR] = (uint8_t)c;
}

static RuntimeValue serial_write_value(RuntimeValue data)
{
    if (IS_HEAP(data)) {
        RuntimeString *s = (RuntimeString *)DECODE_PTR(data);
        if (s && s->hdr.type == HEAP_STRING && s->len < 0x100000u) {
            for (uint32_t i = 0; i < s->len; i++) serial_putchar(s->data[i]);
            return ENCODE_INT((int32_t)s->len);
        }
    }
    return ENCODE_INT(0);
}

RuntimeValue rt_stdout_write(RuntimeValue data)
{
    return serial_write_value(data);
}

RuntimeValue rt_stdout_flush(RuntimeValue data)
{
    (void)data;
    return ENCODE_INT(0);
}

RuntimeValue rt_stderr_write(RuntimeValue data) __attribute__((alias("rt_stdout_write")));
RuntimeValue rt_stderr_flush(RuntimeValue data) __attribute__((alias("rt_stdout_flush")));

extern void spl_start(void) __attribute__((weak));
extern char _stack_top[];

__attribute__((naked, section(".text.entry"))) void _start(void)
{
    __asm__ volatile(
        "la sp, _stack_top\n"
        "la t0, spl_start\n"
        "beqz t0, 1f\n"
        "jalr t0\n"
        "1: wfi\n"
        "j 1b\n"
    );
}
