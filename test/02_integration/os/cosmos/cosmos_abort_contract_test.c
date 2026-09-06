#include <stdint.h>

#define UART1_BASE 0xE0001000U
#define UART_CR 0x00U
#define UART_MR 0x04U
#define UART_SR 0x2CU
#define UART_FIFO 0x30U
#define UART_CR_RXRST (1U << 0)
#define UART_CR_TXRST (1U << 1)
#define UART_CR_RXEN (1U << 2)
#define UART_CR_TXEN (1U << 4)
#define UART_MR_8N1 0x20U
#define UART_SR_TXFULL (1U << 4)

#define PREFETCH_KIND 1U
#define DATA_KIND 2U
#define PREFETCH_STATUS 0x00000005U
#define DATA_STATUS 0x00000805U
#define PREFETCH_ADDRESS 0xDEAD1000U
#define DATA_ADDRESS 0xDEAD0000U
#define EXCEPTION_CLEAR 0x434C4541U
#define EXCEPTION_ACTIVE 0x41435449U

volatile unsigned int cosmos_exception_active = EXCEPTION_CLEAR;
volatile unsigned int cosmos_exception_kind;
volatile unsigned int cosmos_exception_status;
volatile unsigned int cosmos_exception_address;
volatile unsigned int cosmos_exception_pc;
volatile unsigned int cosmos_expected_kind;
volatile unsigned int cosmos_expected_address;
volatile unsigned int cosmos_expected_pc;
volatile unsigned int cosmos_resumed;
static unsigned int cosmos_test_l1[4096] __attribute__((aligned(16384)));

static void uart_put(unsigned int byte) {
    volatile uint32_t *status = (volatile uint32_t *)(UART1_BASE + UART_SR);
    volatile uint32_t *fifo = (volatile uint32_t *)(UART1_BASE + UART_FIFO);
    unsigned int poll;
    for (poll = 0U; poll < 100000U; ++poll) {
        if ((*status & UART_SR_TXFULL) == 0U) {
            *fifo = byte & 0xffU;
            return;
        }
    }
}

static void uart_puts(const char *text) {
    while (*text != '\0') {
        uart_put((unsigned int)(unsigned char)*text);
        ++text;
    }
}

static void uart_hex(unsigned int value) {
    static const char digits[] = "0123456789ABCDEF";
    unsigned int shift;
    for (shift = 28U; ; shift -= 4U) {
        uart_put((unsigned int)digits[(value >> shift) & 0xFU]);
        if (shift == 0U) {
            return;
        }
    }
}

static void uart_init(void) {
    volatile uint32_t *control = (volatile uint32_t *)(UART1_BASE + UART_CR);
    volatile uint32_t *mode = (volatile uint32_t *)(UART1_BASE + UART_MR);
    *control = UART_CR_RXRST | UART_CR_TXRST;
    *mode = UART_MR_8N1;
    *control = UART_CR_TXEN | UART_CR_RXEN;
}

static void enable_test_mmu(void) {
    unsigned int section;
    for (section = 0U; section < 1024U; ++section) {
        cosmos_test_l1[section] = (section << 20) | 0xC0EU;
    }
    cosmos_test_l1[0xE00U] = 0xE0000000U | 0xC0EU;
    __asm__ volatile(
        "mcr p15, 0, %0, c2, c0, 0\n"
        "mov r1, #1\n"
        "mcr p15, 0, r1, c3, c0, 0\n"
        "mcr p15, 0, r1, c8, c7, 0\n"
        "dsb sy\n"
        "mrc p15, 0, r1, c1, c0, 0\n"
        "orr r1, r1, #1\n"
        "mcr p15, 0, r1, c1, c0, 0\n"
        "dsb sy\n"
        "isb sy\n"
        :
        : "r"(cosmos_test_l1)
        : "r1", "memory");
}

static void trigger_data_abort(void)
    __attribute__((noreturn, noinline, unused));
static void trigger_data_abort(void) {
    __asm__ volatile(
        "adr r0, 1f\n"
        "ldr r1, =cosmos_expected_pc\n"
        "str r0, [r1]\n"
        "ldr r1, =0xDEAD0000\n"
        "mov r2, #0x5A\n"
        "1: str r2, [r1]\n"
        ::: "r0", "r1", "r2", "memory");
    cosmos_resumed = 1U;
    for (;;) {
        __asm__ volatile("wfi");
    }
}

static void trigger_prefetch_abort(void)
    __attribute__((noreturn, noinline, unused));
static void trigger_prefetch_abort(void) {
    cosmos_expected_pc = PREFETCH_ADDRESS;
    __asm__ volatile(
        "ldr r4, =0xDEAD1000\n"
        "bx r4\n"
        ::: "r4", "memory");
    cosmos_resumed = 1U;
    for (;;) {
        __asm__ volatile("wfi");
    }
}

__attribute__((noreturn))
void cosmos_exception_halt(unsigned int kind, unsigned int status,
                           unsigned int address, unsigned int pc) {
    unsigned int pass = kind == cosmos_expected_kind &&
        status == (kind == PREFETCH_KIND ? PREFETCH_STATUS : DATA_STATUS) &&
        address == cosmos_expected_address &&
        pc == cosmos_expected_pc && cosmos_resumed == 0U;

    cosmos_exception_active = EXCEPTION_ACTIVE;
    cosmos_exception_kind = kind;
    cosmos_exception_status = status;
    cosmos_exception_address = address;
    cosmos_exception_pc = pc;
    uart_puts("COSMOS_ABORT kind=0x");
    uart_hex(kind);
    uart_puts(" status=0x");
    uart_hex(status);
    uart_puts(" address=0x");
    uart_hex(address);
    uart_puts(" pc=0x");
    uart_hex(pc);
    uart_puts(" resumed=0x");
    uart_hex(cosmos_resumed);
    uart_puts(pass ? " PASS terminal=0x00000001\r\n" :
                   " FAIL terminal=0x00000001\r\n");
    for (;;) {
        __asm__ volatile("cpsid if\n wfi" ::: "memory");
    }
}

void cosmos_smp_secondary_prepare(void) {
    for (;;) {
        __asm__ volatile("wfi");
    }
}

void cosmos_gic_irq_dispatch(void) {
}

void cosmos_boot_main(void) {
    uart_init();
    enable_test_mmu();
#if defined(COSMOS_ABORT_PREFETCH)
    cosmos_expected_kind = PREFETCH_KIND;
    cosmos_expected_address = PREFETCH_ADDRESS;
    uart_puts("COSMOS_ABORT_TRIGGER prefetch\r\n");
    trigger_prefetch_abort();
#else
    cosmos_expected_kind = DATA_KIND;
    cosmos_expected_address = DATA_ADDRESS;
    uart_puts("COSMOS_ABORT_TRIGGER data\r\n");
    trigger_data_abort();
#endif
    cosmos_resumed = 1U;
    for (;;) {
        __asm__ volatile("wfi");
    }
}
