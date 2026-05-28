/*
 * SimpleOS ARM32 minimal startup/stdout capsule.
 *
 * Policy stays in pure Simple; this file owns only PL011 MMIO writes,
 * stdout/stderr ABI hooks, optional spl_start handoff, and WFI halt.
 */

#include <stdint.h>

typedef int32_t RuntimeValue;

#define TAG_MASK    0x7u
#define TAG_INT     0x0u
#define TAG_HEAP    0x1u
#define ENCODE_INT(v) ((RuntimeValue)(((uint32_t)(int32_t)(v) << 3) | TAG_INT))
#define DECODE_PTR(v) ((void *)((uint32_t)(v) & ~TAG_MASK))
#define IS_HEAP(v)    (((uint32_t)(v) & TAG_MASK) == TAG_HEAP)
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

#define PL011_BASE 0x09000000u
#define PL011_DR   (*(volatile uint32_t *)(PL011_BASE + 0x000u))
#define PL011_FR   (*(volatile uint32_t *)(PL011_BASE + 0x018u))
#define PL011_IBRD (*(volatile uint32_t *)(PL011_BASE + 0x024u))
#define PL011_FBRD (*(volatile uint32_t *)(PL011_BASE + 0x028u))
#define PL011_LCRH (*(volatile uint32_t *)(PL011_BASE + 0x02Cu))
#define PL011_CR   (*(volatile uint32_t *)(PL011_BASE + 0x030u))
#define PL011_ICR  (*(volatile uint32_t *)(PL011_BASE + 0x044u))
#define PL011_TXFF (1u << 5)

static void pl011_init(void)
{
    PL011_CR = 0u;
    PL011_ICR = 0x7FFu;
    PL011_IBRD = 13u;
    PL011_FBRD = 1u;
    PL011_LCRH = (3u << 5) | (1u << 4);
    PL011_CR = (1u << 0) | (1u << 8) | (1u << 9);
}

void serial_putchar(char c)
{
    for (uint32_t spin = 0; spin < 100000u; spin++) {
        if ((PL011_FR & PL011_TXFF) == 0u) break;
    }
    PL011_DR = (uint32_t)(uint8_t)c;
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

void _start(void)
{
    pl011_init();
    if (spl_start) spl_start();
    for (;;) {
        __asm__ volatile("wfi");
    }
}
