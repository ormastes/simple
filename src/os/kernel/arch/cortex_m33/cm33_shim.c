#include <stdint.h>

extern uint32_t _sbss, _ebss, _etext;
extern uint32_t _app_sandbox_start, _app_sandbox_end;

/* ── UART ─────────────────────────────────────────────────────── */
#define UART0_BASE 0x40200000
#define UART0_DATA (*(volatile uint32_t *)(UART0_BASE + 0x00))
#define UART0_STATE (*(volatile uint32_t *)(UART0_BASE + 0x04))
#define UART0_CTRL (*(volatile uint32_t *)(UART0_BASE + 0x08))
#define UART0_BAUDDIV (*(volatile uint32_t *)(UART0_BASE + 0x10))

static void uart_init(void) {
    UART0_CTRL = 0x00;
    UART0_BAUDDIV = 16;
    UART0_CTRL = 0x03;
}

static void uart_putc(char c) { UART0_DATA = (uint32_t)c; }

static void uart_puts(const char *s) {
    while (*s) { uart_putc(*s++); }
}

static void uart_putln(const char *s) {
    uart_puts(s);
    uart_putc('\r');
    uart_putc('\n');
}

static void write_hex32(uint32_t v) {
    for (int i = 28; i >= 0; i -= 4) {
        uint8_t n = (v >> i) & 0xF;
        uart_putc(n < 10 ? '0' + n : 'a' + n - 10);
    }
}

static void write_dec(uint32_t v) {
    char tmp[12];
    int i = 0;
    if (v == 0) { uart_putc('0'); return; }
    while (v) { tmp[i++] = '0' + (v % 10); v /= 10; }
    while (i--) uart_putc(tmp[i]);
}

/* ── String helpers ───────────────────────────────────────────── */
static int streq(const char *a, const char *b) {
    while (*a && *b) { if (*a++ != *b++) return 0; }
    return *a == *b;
}

static int starts_with(const char *s, const char *prefix) {
    while (*prefix) { if (*s++ != *prefix++) return 0; }
    return 1;
}

static uint32_t parse_hex(const char *s) {
    if (s[0] == '0' && s[1] == 'x') s += 2;
    uint32_t r = 0;
    while (*s) {
        uint8_t c = *s++;
        uint8_t n;
        if (c >= '0' && c <= '9') n = c - '0';
        else if (c >= 'a' && c <= 'f') n = c - 'a' + 10;
        else if (c >= 'A' && c <= 'F') n = c - 'A' + 10;
        else break;
        r = (r << 4) | n;
    }
    return r;
}

static uint32_t strlen_simple(const char *s) {
    uint32_t n = 0;
    while (*s++) n++;
    return n;
}

static void memcpy_simple(void *dst, const void *src, uint32_t n) {
    uint8_t *d = (uint8_t *)dst;
    const uint8_t *s = (const uint8_t *)src;
    while (n--) *d++ = *s++;
}

/* ── SCB / Fault registers ────────────────────────────────────── */
#define SCB_SHCSR  (*(volatile uint32_t *)0xE000ED24)
#define SCB_CFSR   (*(volatile uint32_t *)0xE000ED28)
#define SCB_HFSR   (*(volatile uint32_t *)0xE000ED2C)
#define SCB_MMFAR  (*(volatile uint32_t *)0xE000ED34)
#define SCB_BFAR   (*(volatile uint32_t *)0xE000ED38)
#define SCB_AIRCR  (*(volatile uint32_t *)0xE000ED0C)

/* ── MPU (ARMv8-M) ────────────────────────────────────────────── */
#define MPU_TYPE   (*(volatile uint32_t *)0xE000ED90)
#define MPU_CTRL   (*(volatile uint32_t *)0xE000ED94)
#define MPU_RNR    (*(volatile uint32_t *)0xE000ED98)
#define MPU_RBAR   (*(volatile uint32_t *)0xE000ED9C)
#define MPU_RLAR   (*(volatile uint32_t *)0xE000EDA0)
#define MPU_MAIR0  (*(volatile uint32_t *)0xE000EDC0)

/* Memory layout (QEMU MPS2-AN505: 32KB SRAM):
 *   0x10000000 - 0x103FFFFF  Flash  4MB  (code + rodata)
 *   0x20000000 - 0x20005FFF  Kernel RAM  24KB (BSS, globals, FS, heap)
 *   0x20006000 - 0x200067FF  App code region  2KB  (.app_sandbox)
 *   0x20006800 - 0x200069FF  App stack  512B  (.app_sandbox)
 *   0x20006A00 - 0x20007FFF  Kernel stack  5.5KB (grows down from 0x20008000)
 *
 * MPU lockdown uses non-overlapping regions (QEMU AN505 ignores priority).
 */
#define APP_STACK_TOP  0x20008000

/* ── SysTick ─────────────────────────────────────────────────── */
#define SYST_CSR  (*(volatile uint32_t *)0xE000E010)
#define SYST_RVR  (*(volatile uint32_t *)0xE000E014)
#define SYST_CVR  (*(volatile uint32_t *)0xE000E018)

/* ── CCR (Configuration and Control Register) ────────────────── */
#define SCB_CCR   (*(volatile uint32_t *)0xE000ED14)

static volatile uint32_t tick_count;
static volatile uint32_t app_running;
static volatile uint32_t app_ticks;
static volatile uint32_t app_was_killed;
static volatile uint32_t exec_return_addr;
static volatile uint32_t fault_expected;
static volatile uint32_t fault_caught;
static volatile uint32_t fault_recovery_pc;
#define APP_TIMEOUT_TICKS 500

#define STACK_CANARY 0xDEADBEEF
static uint32_t mpu_regions;

static void mpu_configure_region(uint32_t region, uint32_t rbar, uint32_t rlar) {
    MPU_RNR = region;
    MPU_RBAR = rbar;
    MPU_RLAR = rlar;
}

static void mpu_init(void) {
    uint32_t mtype = MPU_TYPE;
    mpu_regions = (mtype >> 8) & 0xFF;

    if (mpu_regions == 0) {
        uart_putln("[MPU] No MPU available");
        return;
    }

    MPU_CTRL = 0;

    /* MAIR0: Attr0=normal WB-WA, Attr1=device nGnRnE */
    MPU_MAIR0 = 0x000000FF;

    /* Region 0: Flash 0x10000000-0x103FFFFF, RO+X, Normal */
    /* RBAR: base[31:5] | SH=00 | AP=11(RO any) | XN=0 */
    /* RLAR: limit[31:5] | AT=000(Attr0) | EN=1 */
    mpu_configure_region(0,
        0x10000000 | (0 << 3) | (3 << 1) | 0,
        0x103FFFE0 | (0 << 1) | 1);

    /* Region 1: RAM 0x20000000-0x20007FFF (32KB), RW+X, Normal */
    mpu_configure_region(1,
        0x20000000 | (0 << 3) | (1 << 1) | 0,
        0x20007FE0 | (0 << 1) | 1);

    /* Region 2: Peripherals 0x40000000-0x5FFFFFFF, RW+noX, Device */
    mpu_configure_region(2,
        0x40000000 | (0 << 3) | (1 << 1) | 1,
        0x5FFFFFE0 | (1 << 1) | 1);

    /* Region 3: PPB 0xE0000000-0xE00FFFFF, RW priv-only+noX, Device */
    mpu_configure_region(3,
        0xE0000000 | (0 << 3) | (0 << 1) | 1,
        0xE00FFFE0 | (1 << 1) | 1);

    /* Region 4: reserved for kernel stack lockdown during app exec */

    /* Enable MPU: PRIVDEFENA=1 (default map for privileged), ENABLE=1 */
    MPU_CTRL = (1 << 2) | 1;
    __asm volatile("dsb\nisb" ::: "memory");

    uart_puts("[MPU] Enabled, ");
    write_dec(mpu_regions);
    uart_puts(" regions available, 5 configured");
    uart_putln("");
}

/* ── Fault Handlers ───────────────────────────────────────────── */
static void cfsr_decode(uint32_t cfsr) {
    uart_puts("  CFSR=0x"); write_hex32(cfsr);
    if (!cfsr) { uart_putln(" (clean)"); return; }
    uart_putln("");
    uint8_t mmfsr = cfsr & 0xFF;
    uint8_t bfsr = (cfsr >> 8) & 0xFF;
    uint16_t ufsr = (cfsr >> 16) & 0xFFFF;
    if (mmfsr & 0x01) uart_putln("    IACCVIOL: instruction access violation");
    if (mmfsr & 0x02) uart_putln("    DACCVIOL: data access violation");
    if (mmfsr & 0x08) uart_putln("    MUNSTKERR: MemManage on unstacking");
    if (mmfsr & 0x10) uart_putln("    MSTKERR: MemManage on stacking");
    if (mmfsr & 0x80) {
        uart_puts("    MMFAR=0x"); write_hex32(SCB_MMFAR); uart_putln("");
    }
    if (bfsr & 0x01) uart_putln("    IBUSERR: instruction bus error");
    if (bfsr & 0x02) uart_putln("    PRECISERR: precise data bus error");
    if (bfsr & 0x04) uart_putln("    IMPRECISERR: imprecise data bus error");
    if (bfsr & 0x08) uart_putln("    UNSTKERR: BusFault on unstacking");
    if (bfsr & 0x10) uart_putln("    STKERR: BusFault on stacking");
    if (bfsr & 0x80) {
        uart_puts("    BFAR=0x"); write_hex32(SCB_BFAR); uart_putln("");
    }
    if (ufsr & 0x0001) uart_putln("    UNDEFINSTR: undefined instruction");
    if (ufsr & 0x0002) uart_putln("    INVSTATE: invalid state (ARM/Thumb)");
    if (ufsr & 0x0004) uart_putln("    INVPC: invalid PC load");
    if (ufsr & 0x0008) uart_putln("    NOCP: no coprocessor");
    if (ufsr & 0x0010) uart_putln("    STKOF: stack overflow");
    if (ufsr & 0x0100) uart_putln("    UNALIGNED: unaligned access");
    if (ufsr & 0x0200) uart_putln("    DIVBYZERO: divide by zero");
}

static void fault_dump(const char *name, uint32_t *frame) {
    uart_putln("");
    uart_puts("*** ");
    uart_puts(name);
    uart_putln(" ***");

    uart_puts("  R0 =0x"); write_hex32(frame[0]);
    uart_puts(" R1 =0x"); write_hex32(frame[1]); uart_putln("");
    uart_puts("  R2 =0x"); write_hex32(frame[2]);
    uart_puts(" R3 =0x"); write_hex32(frame[3]); uart_putln("");
    uart_puts("  R12=0x"); write_hex32(frame[4]);
    uart_puts(" LR =0x"); write_hex32(frame[5]); uart_putln("");
    uart_puts("  PC =0x"); write_hex32(frame[6]);
    uart_puts(" xPSR=0x"); write_hex32(frame[7]); uart_putln("");

    cfsr_decode(SCB_CFSR);
    SCB_CFSR = SCB_CFSR;

    uart_putln("System halted.");
    while (1) {}
}

void HardFault_Handler_C(uint32_t *frame);
void HardFault_Handler_C(uint32_t *frame) { fault_dump("HARD FAULT", frame); }

void MemManage_Handler_C(uint32_t *frame);
void MemManage_Handler_C(uint32_t *frame) {
    if (fault_expected) {
        fault_caught = SCB_CFSR & 0xFF;
        SCB_CFSR = SCB_CFSR;
        fault_expected = 0;
        frame[6] = fault_recovery_pc;
        frame[7] |= (1 << 24);
        return;
    }
    if (app_running) {
        uart_puts("[FAULT] App memory violation (CFSR=0x");
        write_hex32(SCB_CFSR);
        uart_putln(") — killed");
        SCB_CFSR = SCB_CFSR;
        app_running = 0;
        app_was_killed = 1;
        frame[6] = exec_return_addr;
        frame[7] |= (1 << 24);
        __asm volatile("movs r0, #0\nmsr control, r0" ::: "r0", "memory");
        return;
    }
    fault_dump("MEMMANAGE FAULT", frame);
}

void BusFault_Handler_C(uint32_t *frame);
void BusFault_Handler_C(uint32_t *frame) { fault_dump("BUS FAULT", frame); }

void UsageFault_Handler_C(uint32_t *frame);
void UsageFault_Handler_C(uint32_t *frame) { fault_dump("USAGE FAULT", frame); }

void HardFault_Handler(void) __attribute__((naked));
void HardFault_Handler(void) {
    __asm volatile(
        "tst lr, #4\n"
        "ite eq\n"
        "mrseq r0, msp\n"
        "mrsne r0, psp\n"
        "b HardFault_Handler_C\n"
    );
}

void MemManage_Handler(void) __attribute__((naked));
void MemManage_Handler(void) {
    __asm volatile(
        "tst lr, #4\n"
        "ite eq\n"
        "mrseq r0, msp\n"
        "mrsne r0, psp\n"
        "b MemManage_Handler_C\n"
    );
}

void BusFault_Handler(void) __attribute__((naked));
void BusFault_Handler(void) {
    __asm volatile(
        "tst lr, #4\n"
        "ite eq\n"
        "mrseq r0, msp\n"
        "mrsne r0, psp\n"
        "b BusFault_Handler_C\n"
    );
}

void UsageFault_Handler(void) __attribute__((naked));
void UsageFault_Handler(void) {
    __asm volatile(
        "tst lr, #4\n"
        "ite eq\n"
        "mrseq r0, msp\n"
        "mrsne r0, psp\n"
        "b UsageFault_Handler_C\n"
    );
}

void SysTick_Handler_C(uint32_t *frame);
void SysTick_Handler_C(uint32_t *frame) {
    tick_count++;
    if (app_running) {
        app_ticks++;
        if (app_ticks >= APP_TIMEOUT_TICKS) {
            app_running = 0;
            app_was_killed = 1;
            frame[6] = exec_return_addr;
            frame[7] |= (1 << 24);
            __asm volatile("movs r0, #0\nmsr control, r0" ::: "r0", "memory");
        }
    }
}

void SysTick_Handler(void) __attribute__((naked));
void SysTick_Handler(void) {
    __asm volatile(
        "tst lr, #4\n"
        "ite eq\n"
        "mrseq r0, msp\n"
        "mrsne r0, psp\n"
        "b SysTick_Handler_C\n"
    );
}

/* ── SVC Handler (system calls for apps) ─────────────────────── */
/* SVC #0: putchar(r0=char)  SVC #1: exit app */
void SVCall_Handler_C(uint32_t *frame);
void SVCall_Handler_C(uint32_t *frame) {
    uint16_t *pc = (uint16_t *)(frame[6] - 2);
    uint8_t svc_num = ((uint8_t *)pc)[0];

    switch (svc_num) {
    case 0:
        uart_putc((char)(frame[0] & 0xFF));
        break;
    case 1:
        app_running = 0;
        frame[6] = exec_return_addr;
        frame[7] |= (1 << 24);
        __asm volatile("movs r0, #0\nmsr control, r0" ::: "r0", "memory");
        break;
    default:
        uart_puts("[SVC] Unknown: ");
        write_dec(svc_num);
        uart_putln("");
        break;
    }
}

void SVCall_Handler(void) __attribute__((naked));
void SVCall_Handler(void) {
    __asm volatile(
        "tst lr, #4\n"
        "ite eq\n"
        "mrseq r0, msp\n"
        "mrsne r0, psp\n"
        "b SVCall_Handler_C\n"
    );
}

static void faults_init(void) {
    SCB_SHCSR |= (1 << 16) | (1 << 17) | (1 << 18);
    SCB_CCR |= (1 << 4);
    uart_putln("[FAULT] MemManage, BusFault, UsageFault enabled; DIV0 trap on");
}

static void systick_init(void) {
    SYST_RVR = 250000 - 1;
    SYST_CVR = 0;
    SYST_CSR = 0x07;
    uart_putln("[TICK] SysTick enabled (~100 Hz)");
}

/* ── In-Memory Filesystem ─────────────────────────────────────── */
#define FS_MAX_FILES 16
#define FS_NAME_MAX  32

struct fs_file {
    char name[FS_NAME_MAX];
    uint8_t *data;
    uint32_t size;
    uint32_t flags;  /* bit 0: executable */
};

static struct fs_file fs_table[FS_MAX_FILES];
static uint32_t fs_count;
static uint8_t fs_storage[4096];
static uint32_t fs_used;
static uint8_t app_region[2048] __attribute__((aligned(32), section(".app_sandbox")));
static uint8_t app_stack[512] __attribute__((aligned(8), section(".app_sandbox")));

static void mpu_lockdown_for_app(void) {
    /* QEMU AN505 faults on overlapping regions even with correct priority,
     * so we disable the MPU during reconfiguration to avoid transient overlaps.
     *
     * Region 1: Kernel data   0x20000000-0x20005FFF  priv-only, XN
     * Region 4: Kernel stack  0x20006A00-0x20007FFF  priv-only, XN
     * Region 5: App sandbox   0x20006000-0x200069FF  RW any-priv, X
     */
    __asm volatile("cpsid i" ::: "memory");
    MPU_CTRL = 0;
    __asm volatile("dsb\nisb" ::: "memory");

    mpu_configure_region(1,
        0x20000000 | (0 << 3) | (0 << 1) | 1,   /* AP=00 priv-only, XN=1 */
        0x20005FE0 | (0 << 1) | 1);

    mpu_configure_region(4,
        0x20006A00 | (0 << 3) | (0 << 1) | 1,   /* AP=00 priv-only, XN=1 */
        0x20007FE0 | (0 << 1) | 1);

    mpu_configure_region(5,
        0x20006000 | (0 << 3) | (1 << 1) | 0,   /* AP=01 RW any, XN=0 */
        0x200069E0 | (0 << 1) | 1);

    MPU_CTRL = (1 << 2) | 1;
    __asm volatile("dsb\nisb" ::: "memory");
    __asm volatile("cpsie i" ::: "memory");
}

static void mpu_restore_after_app(void) {
    __asm volatile("cpsid i" ::: "memory");
    MPU_CTRL = 0;
    __asm volatile("dsb\nisb" ::: "memory");

    mpu_configure_region(1,
        0x20000000 | (0 << 3) | (1 << 1) | 0,   /* AP=01 RW any, XN=0 */
        0x20007FE0 | (0 << 1) | 1);
    mpu_configure_region(4, 0, 0);
    mpu_configure_region(5, 0, 0);

    MPU_CTRL = (1 << 2) | 1;
    __asm volatile("dsb\nisb" ::: "memory");
    __asm volatile("cpsie i" ::: "memory");
}

/* Prints "Hello from app!\r\n" via SVC#0 (putchar syscall), returns */
static const uint8_t hello_app[] = {
    /* 'H' */ 0x48, 0x20, 0x00, 0xdf,  /* movs r0, #'H'; svc #0 */
    /* 'e' */ 0x65, 0x20, 0x00, 0xdf,
    /* 'l' */ 0x6c, 0x20, 0x00, 0xdf,
    /* 'l' */ 0x6c, 0x20, 0x00, 0xdf,
    /* 'o' */ 0x6f, 0x20, 0x00, 0xdf,
    /* ' ' */ 0x20, 0x20, 0x00, 0xdf,
    /* 'f' */ 0x66, 0x20, 0x00, 0xdf,
    /* 'r' */ 0x72, 0x20, 0x00, 0xdf,
    /* 'o' */ 0x6f, 0x20, 0x00, 0xdf,
    /* 'm' */ 0x6d, 0x20, 0x00, 0xdf,
    /* ' ' */ 0x20, 0x20, 0x00, 0xdf,
    /* 'a' */ 0x61, 0x20, 0x00, 0xdf,
    /* 'p' */ 0x70, 0x20, 0x00, 0xdf,
    /* 'p' */ 0x70, 0x20, 0x00, 0xdf,
    /* '!' */ 0x21, 0x20, 0x00, 0xdf,
    /* '\r' */ 0x0d, 0x20, 0x00, 0xdf,
    /* '\n' */ 0x0a, 0x20, 0x00, 0xdf,
    /* bx lr */
    0x70, 0x47,
};

/* Counter app: prints 1-5 via SVC#0, returns */
static const uint8_t count_app[] = {
    /* movs r4, #'1' */
    0x31, 0x24,
    /* loop: mov r0, r4 */
    0x20, 0x46,
    /* svc #0 */
    0x00, 0xdf,
    /* adds r4, #1 */
    0x01, 0x34,
    /* cmp r4, #'6' */
    0x36, 0x2c,
    /* bne loop */
    0xfa, 0xd1,
    /* movs r0, #'\r'; svc #0 */
    0x0d, 0x20, 0x00, 0xdf,
    /* movs r0, #'\n'; svc #0 */
    0x0a, 0x20, 0x00, 0xdf,
    /* bx lr */
    0x70, 0x47,
};

/* Infinite loop app: spins forever (tests SysTick timeout kill) */
static const uint8_t spin_app[] = {
    /* b . (branch to self) */
    0xfe, 0xe7,
};

/* Rogue app: tries to read kernel data at 0x20000000 — should DACCVIOL */
static const uint8_t rogue_app[] = {
    /* ldr r0, =0x20000000 */
    0x4f, 0xf0, 0x00, 0x00,  /* mov.w r0, #0 */
    0xc0, 0xf2, 0x00, 0x00,  /* movt  r0, #0x2000 */
    /* ldr r1, [r0] — read kernel data */
    0x01, 0x68,
    /* bx lr */
    0x70, 0x47,
};

/* SVC-based hello: uses syscall 0 (putchar) instead of direct UART */
static const uint8_t svc_hello_app[] = {
    /* 'H' */ 0x48, 0x20, 0x00, 0xdf,  /* movs r0, #'H'; svc #0 */
    /* 'i' */ 0x69, 0x20, 0x00, 0xdf,
    /* '!' */ 0x21, 0x20, 0x00, 0xdf,
    /* '\r' */ 0x0d, 0x20, 0x00, 0xdf,
    /* '\n' */ 0x0a, 0x20, 0x00, 0xdf,
    /* bx lr */
    0x70, 0x47,
};

static void fs_add_file(const char *name, const uint8_t *src, uint32_t size, uint32_t flags) {
    if (fs_count >= FS_MAX_FILES) return;
    if (fs_used + size > sizeof(fs_storage)) return;
    struct fs_file *f = &fs_table[fs_count];
    const char *n = name;
    int i = 0;
    while (*n && i < FS_NAME_MAX - 1) f->name[i++] = *n++;
    f->name[i] = '\0';
    f->data = &fs_storage[fs_used];
    f->size = size;
    f->flags = flags;
    memcpy_simple(&fs_storage[fs_used], src, size);
    fs_used += (size + 3) & ~3u;
    fs_count++;
}

static const char readme_text[] =
    "SimpleOS Lite v0.5 (hardened)\r\n"
    "A minimal OS for Cortex-M33.\r\n"
    "Features: non-overlapping MPU, unprivileged apps, SVC syscalls,\r\n"
    "  fault decode, SysTick timeout, stack canary, flash CRC\r\n"
    "Commands: help, ls, cat, exec, peek, poke, mpu, faults, uptime, stack\r\n";

static void fs_init(void) {
    fs_count = 0;
    fs_used = 0;
    fs_add_file("readme.txt", (const uint8_t *)readme_text, sizeof(readme_text) - 1, 0);
    fs_add_file("hello.bin", hello_app, sizeof(hello_app), 1);
    fs_add_file("count.bin", count_app, sizeof(count_app), 1);
    fs_add_file("spin.bin", spin_app, sizeof(spin_app), 1);
    fs_add_file("svc_hi.bin", svc_hello_app, sizeof(svc_hello_app), 1);
    fs_add_file("rogue.bin", rogue_app, sizeof(rogue_app), 1);
    uart_puts("[FS] In-memory filesystem: ");
    write_dec(fs_count);
    uart_puts(" files, ");
    write_dec(fs_used);
    uart_putln(" bytes used");
}

static struct fs_file *fs_find(const char *name) {
    for (uint32_t i = 0; i < fs_count; i++) {
        if (streq(fs_table[i].name, name)) return &fs_table[i];
    }
    return (struct fs_file *)0;
}

/* ── Shell Commands ───────────────────────────────────────────── */
static void cmd_help(void) {
    uart_putln("SimpleOS Lite Shell Commands:");
    uart_putln("  help           - show this message");
    uart_putln("  info           - system information");
    uart_putln("  echo <text>    - print text");
    uart_putln("  peek <addr>    - read 32-bit word at hex address");
    uart_putln("  poke <a> <v>   - write 32-bit value to address");
    uart_putln("  ls             - list files");
    uart_putln("  cat <file>     - display file contents");
    uart_putln("  exec <file>    - run executable (5s timeout)");
    uart_putln("  mpu            - show MPU status");
    uart_putln("  faults         - show fault status");
    uart_putln("  uptime         - show system uptime");
    uart_putln("  stack          - show stack usage and canary");
    uart_putln("  selftest       - run security self-test");
    uart_putln("  reboot         - reset the system");
}

static void cmd_info(void) {
    uart_putln("SimpleOS Lite v0.5 (hardened)");
    uart_putln("  CPU:      ARM Cortex-M33 (ARMv8-M Mainline)");
    uart_putln("  Platform: MPS2-AN505 (QEMU)");
    uart_putln("  Flash:    0x10000000 (4 MB)");
    uart_putln("  RAM:      0x20000000 (32 KB)");
    uart_putln("  UART:     CMSDK APB @ 0x40200000");
    uart_puts("  MPU:      ");
    write_dec(mpu_regions);
    uart_putln(" regions");
    uart_puts("  FS files: ");
    write_dec(fs_count);
    uart_putln("");
    uart_puts("  CCR:      0x"); write_hex32(SCB_CCR); uart_putln("");
    uart_puts("  Uptime:   ");
    write_dec(tick_count / 100);
    uart_putln("s");
}

static void cmd_ls(void) {
    for (uint32_t i = 0; i < fs_count; i++) {
        struct fs_file *f = &fs_table[i];
        uart_puts("  ");
        write_dec(f->size);
        uart_puts("\t");
        if (f->flags & 1) uart_puts("[x] ");
        else uart_puts("    ");
        uart_putln(f->name);
    }
}

static void cmd_cat(const char *name) {
    struct fs_file *f = fs_find(name);
    if (!f) {
        uart_puts("file not found: ");
        uart_putln(name);
        return;
    }
    for (uint32_t i = 0; i < f->size; i++) {
        uart_putc((char)f->data[i]);
    }
}

/* Exit trampoline in Flash: apps return here via bx lr → SVC#1 → clean exit */
static void __attribute__((naked, used)) app_exit_trampoline(void) {
    __asm volatile("svc #1\nb .\n");
}

/* Unprivileged PSP-isolated exec: CONTROL=#3 (nPRIV=1 + SPSEL=1).
 * Apps run unprivileged on PSP, MPU AP=00 regions block data access,
 * XN=1 prevents code execution from kernel regions.
 * LR is set to app_exit_trampoline so app's bx lr triggers SVC#1 exit.
 * Handlers clear CONTROL before returning to kernel Thread mode.
 */
static void __attribute__((naked, used)) exec_with_psp(uint32_t entry_thumb, uint32_t psp_top) {
    __asm volatile(
        "stmdb sp!, {r4-r11, lr}\n"
        "movw r4, :lower16:exec_return_addr\n"
        "movt r4, :upper16:exec_return_addr\n"
        "adr r5, 1f\n"
        "str r5, [r4]\n"
        "msr psp, r1\n"
        "movs r2, #3\n"
        "msr control, r2\n"
        "isb\n"
        "movw lr, :lower16:app_exit_trampoline\n"
        "movt lr, :upper16:app_exit_trampoline\n"
        "orr lr, lr, #1\n"
        "bx r0\n"
        "1:\n"
        "movs r2, #0\n"
        "msr control, r2\n"
        "isb\n"
        "ldmia sp!, {r4-r11, pc}\n"
    );
}

static void cmd_exec(const char *name) {
    struct fs_file *f = fs_find(name);
    if (!f) {
        uart_puts("file not found: ");
        uart_putln(name);
        return;
    }
    if (!(f->flags & 1)) {
        uart_putln("not executable");
        return;
    }

    if (f->size > sizeof(app_region)) {
        uart_putln("binary too large");
        return;
    }

    uart_puts("[EXEC] Loading ");
    uart_puts(name);
    uart_puts(" (");
    write_dec(f->size);
    uart_putln(" bytes)");

    memcpy_simple(app_region, f->data, f->size);
    __asm volatile("dsb\nisb" ::: "memory");

    app_running = 1;
    app_ticks = 0;
    app_was_killed = 0;

    uint32_t entry_addr = (uint32_t)app_region | 1;
    uint32_t app_sp = (uint32_t)app_stack + sizeof(app_stack);

    uart_putln("[EXEC] Running (unprivileged, PSP, MPU locked)...");
    mpu_lockdown_for_app();
    exec_with_psp(entry_addr, app_sp);
    mpu_restore_after_app();

    app_running = 0;
    if (app_was_killed) {
        uart_putln("[EXEC] KILLED (timeout)");
    } else {
        uart_putln("[EXEC] App returned.");
    }
}

static int addr_readable(uint32_t addr) {
    if (addr >= 0x10000000 && addr < 0x10400000) return 1;
    if (addr >= 0x20000000 && addr < 0x20008000) return 1;
    if (addr >= 0x40000000 && addr < 0x60000000) return 1;
    if (addr >= 0xE000E000 && addr < 0xE0100000) return 1;
    return 0;
}

static void cmd_peek(const char *arg) {
    uint32_t addr = parse_hex(arg);
    if ((addr & 3) != 0) { uart_putln("error: address not 4-byte aligned"); return; }
    if (!addr_readable(addr)) {
        uart_putln("error: address not in readable region");
        return;
    }
    uint32_t val = *(volatile uint32_t *)addr;
    uart_putc('[');
    write_hex32(addr);
    uart_puts("] = 0x");
    write_hex32(val);
    uart_putln("");
}

static int addr_writable(uint32_t addr) {
    if (addr >= 0x20000000 && addr < 0x20008000) return 1;
    if (addr >= 0x40000000 && addr < 0x60000000) return 1;
    return 0;
}

static void cmd_poke(const char *arg) {
    uint32_t addr = parse_hex(arg);
    const char *p = arg;
    while (*p && *p != ' ') p++;
    if (!*p) { uart_putln("usage: poke <addr> <val>"); return; }
    p++;
    if ((addr & 3) != 0) { uart_putln("error: address not 4-byte aligned"); return; }
    if (!addr_writable(addr)) {
        uart_putln("error: address not in writable region (RAM/peripherals)");
        return;
    }
    uint32_t val = parse_hex(p);
    *(volatile uint32_t *)addr = val;
    uart_putc('[');
    write_hex32(addr);
    uart_puts("] <- 0x");
    write_hex32(val);
    uart_putln("");
}

static void cmd_mpu(void) {
    uart_puts("MPU_TYPE = 0x"); write_hex32(MPU_TYPE); uart_putln("");
    uart_puts("MPU_CTRL = 0x"); write_hex32(MPU_CTRL); uart_putln("");
    for (uint32_t i = 0; i < 8 && i < mpu_regions; i++) {
        MPU_RNR = i;
        uint32_t rbar = MPU_RBAR;
        uint32_t rlar = MPU_RLAR;
        if (!(rlar & 1)) continue;
        uart_puts("  R"); write_dec(i);
        uart_puts(": RBAR=0x"); write_hex32(rbar);
        uart_puts(" RLAR=0x"); write_hex32(rlar);
        uart_putln("");
    }
}

static void cmd_faults(void) {
    uart_puts("SHCSR = 0x"); write_hex32(SCB_SHCSR); uart_putln("");
    cfsr_decode(SCB_CFSR);
    uart_puts("HFSR  = 0x"); write_hex32(SCB_HFSR); uart_putln("");
}

static void cmd_uptime(void) {
    uint32_t t = tick_count;
    uint32_t secs = t / 100;
    uint32_t ms = (t % 100) * 10;
    write_dec(secs);
    uart_putc('.');
    if (ms < 100) uart_putc('0');
    if (ms < 10) uart_putc('0');
    write_dec(ms);
    uart_puts("s (");
    write_dec(t);
    uart_putln(" ticks)");
}

static void cmd_stack(void) {
    uint32_t sp;
    __asm volatile("mov %0, sp" : "=r"(sp));
    uart_puts("  SP     = 0x"); write_hex32(sp); uart_putln("");
    uart_puts("  Top    = 0x20008000"); uart_putln("");
    uart_puts("  Used   = ");
    write_dec(0x20008000 - sp);
    uart_putln(" bytes");
    uart_puts("  Free   = ");
    write_dec(sp - (uint32_t)&_ebss);
    uart_putln(" bytes (to BSS end)");

    uint32_t canary_loc = ((uint32_t)&_ebss + 3) & ~3u;
    uint32_t canary_val = *(volatile uint32_t *)canary_loc;
    uart_puts("  Canary = 0x"); write_hex32(canary_val);
    if (canary_val == STACK_CANARY) uart_putln(" OK");
    else uart_putln(" CORRUPTED!");
}

static uint32_t flash_crc;

static uint32_t compute_flash_crc(void) {
    volatile uint32_t *p = (volatile uint32_t *)0x10000000;
    uint32_t crc = 0xFFFFFFFF;
    volatile uint32_t *end = (volatile uint32_t *)&_etext;
    while (p < end) {
        uint32_t w = *p++;
        crc ^= w;
        for (int i = 0; i < 32; i++) {
            if (crc & 1) crc = (crc >> 1) ^ 0xEDB88320;
            else crc >>= 1;
        }
    }
    return crc ^ 0xFFFFFFFF;
}

static void __attribute__((naked, used)) try_fault_call(uint32_t target_thumb_addr) {
    __asm volatile(
        "push {r4, lr}\n"
        "movw r4, :lower16:fault_recovery_pc\n"
        "movt r4, :upper16:fault_recovery_pc\n"
        "adr r1, 1f\n"
        "str r1, [r4]\n"
        "blx r0\n"
        "1:\n"
        "pop {r4, pc}\n"
    );
}

static void cmd_selftest(void) {
    int pass = 0, fail = 0;

    /* 1. Stack canary */
    uint32_t canary_loc = ((uint32_t)&_ebss + 3) & ~3u;
    uint32_t cv = *(volatile uint32_t *)canary_loc;
    uart_puts("  [1] Stack canary: ");
    if (cv == STACK_CANARY) { uart_putln("PASS"); pass++; }
    else { uart_putln("FAIL"); fail++; }

    /* 2. Flash integrity */
    uart_puts("  [2] Flash CRC:    ");
    uint32_t crc_now = compute_flash_crc();
    if (crc_now == flash_crc) { uart_putln("PASS"); pass++; }
    else { uart_putln("FAIL (modified!)"); fail++; }

    /* 3. MPU active */
    uart_puts("  [3] MPU enabled:  ");
    if (MPU_CTRL & 1) { uart_putln("PASS"); pass++; }
    else { uart_putln("FAIL"); fail++; }

    /* 4. Fault handlers */
    uart_puts("  [4] Faults on:    ");
    uint32_t sh = SCB_SHCSR;
    if ((sh & ((1<<16)|(1<<17)|(1<<18))) == ((1<<16)|(1<<17)|(1<<18))) {
        uart_putln("PASS"); pass++;
    } else { uart_putln("FAIL"); fail++; }

    /* 5. DIV0 trap */
    uart_puts("  [5] DIV0 trap:    ");
    if (SCB_CCR & (1<<4)) { uart_putln("PASS"); pass++; }
    else { uart_putln("FAIL"); fail++; }

    /* 6. SysTick running */
    uart_puts("  [6] SysTick:      ");
    if (tick_count > 0) { uart_putln("PASS"); pass++; }
    else { uart_putln("FAIL"); fail++; }

    /* 7. XN enforcement (kernel BSS not executable during lockdown) */
    uart_puts("  [7] XN enforce:   ");
    fault_expected = 1;
    fault_caught = 0;
    mpu_lockdown_for_app();
    try_fault_call((uint32_t)&_sbss | 1);
    mpu_restore_after_app();
    if (fault_caught & 0x01) { uart_putln("PASS"); pass++; }
    else { uart_putln("FAIL (XN not enforced)"); fail++; }

    /* 8. AP-deny (rogue app reading kernel data gets DACCVIOL) */
    uart_puts("  [8] AP-deny:      ");
    app_was_killed = 0;
    cmd_exec("rogue.bin");
    if (app_was_killed) { uart_putln("PASS"); pass++; }
    else { uart_putln("FAIL (kernel read not blocked)"); fail++; }

    uart_puts("  Result: ");
    write_dec(pass);
    uart_puts("/");
    write_dec(pass + fail);
    uart_putln(fail ? " SOME FAILED" : " ALL PASSED");
}

/* ── Shell ────────────────────────────────────────────────────── */
static char shell_buf[128];
static int shell_pos;

static void shell(void) {
    uart_putln("SimpleOS Lite v0.5 (hardened) - Cortex-M33");
    uart_putln("Type 'help' for commands.");
    uart_putln("");
    uart_puts("simpleos> ");

    while (1) {
        while (!(UART0_STATE & 2)) {}
        uint32_t ch = UART0_DATA & 0xFF;

        if (ch == '\r' || ch == '\n') {
            uart_putc('\r');
            uart_putc('\n');
            shell_buf[shell_pos] = '\0';
            if (shell_pos > 0) {
                if (streq(shell_buf, "help")) cmd_help();
                else if (streq(shell_buf, "info")) cmd_info();
                else if (streq(shell_buf, "ls")) cmd_ls();
                else if (streq(shell_buf, "mpu")) cmd_mpu();
                else if (streq(shell_buf, "faults")) cmd_faults();
                else if (streq(shell_buf, "uptime")) cmd_uptime();
                else if (streq(shell_buf, "stack")) cmd_stack();
                else if (streq(shell_buf, "selftest")) cmd_selftest();
                else if (streq(shell_buf, "reboot")) {
                    uart_putln("Resetting...");
                    SCB_AIRCR = 0x05FA0004;
                    while(1) {}
                }
                else if (starts_with(shell_buf, "echo ")) uart_putln(shell_buf + 5);
                else if (starts_with(shell_buf, "peek ")) cmd_peek(shell_buf + 5);
                else if (starts_with(shell_buf, "poke ")) cmd_poke(shell_buf + 5);
                else if (starts_with(shell_buf, "cat ")) cmd_cat(shell_buf + 4);
                else if (starts_with(shell_buf, "exec ")) cmd_exec(shell_buf + 5);
                else {
                    uart_puts("unknown command: ");
                    uart_putln(shell_buf);
                }
            }
            shell_pos = 0;
            uart_puts("simpleos> ");
            continue;
        }

        if (ch == 0x7F || ch == 0x08) {
            if (shell_pos > 0) {
                shell_pos--;
                uart_putc(0x08);
                uart_putc(' ');
                uart_putc(0x08);
            }
            continue;
        }

        if (shell_pos < 127) {
            shell_buf[shell_pos++] = (char)ch;
            UART0_DATA = ch;
        }
    }
}

/* ── Boot ─────────────────────────────────────────────────────── */

void _c_main(void);

void Reset_Handler(void) __attribute__((naked, noreturn));
void Reset_Handler(void) {
    __asm volatile (
        "movw r0, #0x8000\n"
        "movt r0, #0x2000\n"
        "mov sp, r0\n"
        "bl _c_main\n"
        "b .\n"
    );
}

void _c_main(void) {
    uint32_t *p = &_sbss;
    while (p < &_ebss) *p++ = 0;

    /* Clear app sandbox (separate linker section at 0x20006000) */
    p = &_app_sandbox_start;
    while (p < &_app_sandbox_end) *p++ = 0;

    uart_init();
    uart_putln("");
    uart_putln("[BOOT] SimpleOS Lite v0.5 - Cortex-M33 (ARMv8-M)");
    uart_putln("[BOOT] Platform: MPS2-AN505 (QEMU)");
    uart_putln("[BOOT] UART0 initialized at 0x40200000");

    /* Plant stack canary at BSS end */
    uint32_t canary_loc = ((uint32_t)&_ebss + 3) & ~3u;
    *(volatile uint32_t *)canary_loc = STACK_CANARY;

    faults_init();
    mpu_init();
    systick_init();
    fs_init();

    flash_crc = compute_flash_crc();
    uart_puts("[BOOT] Flash CRC: 0x"); write_hex32(flash_crc); uart_putln("");

    /* Boot self-test */
    uint32_t cv = *(volatile uint32_t *)canary_loc;
    if (cv != STACK_CANARY) {
        uart_putln("[BOOT] WARNING: stack canary corrupt after init!");
    }

    uart_putln("[BOOT] Entering shell...");
    uart_putln("");

    shell();
}

void Default_Handler(void) __attribute__((naked));
void Default_Handler(void) { __asm volatile("b ."); }

typedef void (*vector_fn)(void);

__attribute__((used, section(".vector_table"), aligned(512)))
const union { uint32_t w; vector_fn fn; } vectors[16] = {
    [0]  = { .w  = 0x20008000 },
    [1]  = { .fn = Reset_Handler },
    [2]  = { .fn = Default_Handler },
    [3]  = { .fn = HardFault_Handler },
    [4]  = { .fn = MemManage_Handler },
    [5]  = { .fn = BusFault_Handler },
    [6]  = { .fn = UsageFault_Handler },
    [7]  = { .fn = Default_Handler },
    [8]  = { .fn = Default_Handler },
    [9]  = { .fn = Default_Handler },
    [10] = { .fn = Default_Handler },
    [11] = { .fn = SVCall_Handler },
    [12] = { .fn = Default_Handler },
    [13] = { .fn = Default_Handler },
    [14] = { .fn = Default_Handler },
    [15] = { .fn = SysTick_Handler },
};
