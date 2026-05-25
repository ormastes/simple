#include <stdint.h>

#if defined(TARGET_RA4M1)
#include "board_ra4m1_uno_r4.h"
#elif defined(TARGET_STM32U585)
#include "board_stm32u585.h"
#else
#include "board_an505.h"
#endif

extern uint32_t _sbss, _ebss, _etext, _stack_top;
extern uint32_t _app_sandbox_start, _app_sandbox_end;

/* ── UART wrappers ────────────────────────────────────────────── */
static void uart_init(void) {
    board_clock_init();
    board_uart_init();
}

static void uart_putc(char c) { board_uart_putc(c); }

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
#define SCB_VTOR   (*(volatile uint32_t *)0xE000ED08)
#define SCB_SHCSR  (*(volatile uint32_t *)0xE000ED24)
#define SCB_CFSR   (*(volatile uint32_t *)0xE000ED28)
#define SCB_HFSR   (*(volatile uint32_t *)0xE000ED2C)
#define SCB_MMFAR  (*(volatile uint32_t *)0xE000ED34)
#define SCB_BFAR   (*(volatile uint32_t *)0xE000ED38)
#define SCB_AIRCR  (*(volatile uint32_t *)0xE000ED0C)

/* ── MPU registers (common to PMSAv7 and PMSAv8-M) ──────────── */
#define MPU_TYPE   (*(volatile uint32_t *)0xE000ED90)
#define MPU_CTRL   (*(volatile uint32_t *)0xE000ED94)
#define MPU_RNR    (*(volatile uint32_t *)0xE000ED98)
#define MPU_RBAR   (*(volatile uint32_t *)0xE000ED9C)
/* 0xE000EDA0 is RLAR on v8 or RASR on v7 — same address, different encoding */
#ifdef BOARD_MPU_V7
#define MPU_RASR   (*(volatile uint32_t *)0xE000EDA0)
#else
#define MPU_RLAR   (*(volatile uint32_t *)0xE000EDA0)
#define MPU_MAIR0  (*(volatile uint32_t *)0xE000EDC0)
#endif

/* ── SysTick ─────────────────────────────────────────────────── */
#define SYST_CSR  (*(volatile uint32_t *)0xE000E010)
#define SYST_RVR  (*(volatile uint32_t *)0xE000E014)
#define SYST_CVR  (*(volatile uint32_t *)0xE000E018)

/* ── CCR ─────────────────────────────────────────────────────── */
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

static void mpu_configure_region(uint32_t region, uint32_t rbar, uint32_t rattr) {
    MPU_RNR = region;
    MPU_RBAR = rbar;
#ifdef BOARD_MPU_V7
    MPU_RASR = rattr;
#else
    MPU_RLAR = rattr;
#endif
}

static void mpu_init(void) {
    uint32_t mtype = MPU_TYPE;
    mpu_regions = (mtype >> 8) & 0xFF;

    if (mpu_regions == 0) {
        uart_putln("[MPU] No MPU available");
        return;
    }

    MPU_CTRL = 0;

#ifdef BOARD_MPU_V7
    /* PMSAv7: TEX/C/B/S bits encoded in RASR per region */
    mpu_configure_region(0, MPU_FLASH_RBAR, MPU_FLASH_RASR);
    mpu_configure_region(1, MPU_RAM_RBAR, MPU_RAM_RASR_OPEN);
    mpu_configure_region(2, MPU_PERIPH_RBAR, MPU_PERIPH_RASR);
    mpu_configure_region(3, MPU_PPB_RBAR, MPU_PPB_RASR);
#else
    /* PMSAv8-M: MAIR holds memory attributes, RBAR/RLAR encode region */
    MPU_MAIR0 = 0x000000FF;  /* Attr0=Normal WB-WA, Attr1=Device nGnRnE */

    mpu_configure_region(0,
        MPU_FLASH_BASE | (0 << 3) | (3 << 1) | 0,
        MPU_FLASH_LIMIT | (0 << 1) | 1);
    mpu_configure_region(1,
        MPU_RAM_BASE | (0 << 3) | (1 << 1) | 0,
        MPU_RAM_LIMIT | (0 << 1) | 1);
    mpu_configure_region(2,
        0x40000000 | (0 << 3) | (1 << 1) | 1,
        0x5FFFFFE0 | (1 << 1) | 1);
    mpu_configure_region(3,
        0xE0000000 | (0 << 3) | (0 << 1) | 1,
        0xE00FFFE0 | (1 << 1) | 1);
#endif

    MPU_CTRL = (1 << 2) | 1;  /* PRIVDEFENA + ENABLE */
    __asm volatile("dsb\nisb" ::: "memory");

    uart_puts("[MPU] Enabled, ");
    write_dec(mpu_regions);
    uart_puts(" regions available, 4 configured");
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

/* ── SVC Handler ─────────────────────────────────────────────── */
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
    SYST_RVR = BOARD_SYSTICK_RELOAD;
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
    uint32_t flags;
};

static struct fs_file fs_table[FS_MAX_FILES];
static uint32_t fs_count;
static uint8_t fs_storage[4096];
static uint32_t fs_used;
static uint8_t app_region[BOARD_APP_REGION_SIZE] __attribute__((aligned(32), section(".app_sandbox")));
static uint8_t app_stack[BOARD_APP_STACK_SIZE] __attribute__((aligned(8), section(".app_sandbox")));

static void mpu_lockdown_for_app(void) {
    __asm volatile("cpsid i" ::: "memory");
    MPU_CTRL = 0;
    __asm volatile("dsb\nisb" ::: "memory");

#ifdef BOARD_MPU_V7
    /* PMSAv7: Region 1 locks all RAM priv-only; Region 5 opens sandbox
     * by higher-number priority (correct on real Cortex-M4 hardware). */
    mpu_configure_region(1, MPU_RAM_RBAR, MPU_RAM_RASR_LOCKED);
    mpu_configure_region(5, MPU_APP_BASE, MPU_APP_RASR);
#else
    /* PMSAv8-M: Non-overlapping regions (required for QEMU AN505). */
    mpu_configure_region(1,
        MPU_RAM_BASE | (0 << 3) | (0 << 1) | 1,   /* priv-only, XN */
        MPU_KDATA_LIMIT | (0 << 1) | 1);
    mpu_configure_region(4,
        MPU_KSTACK_BASE | (0 << 3) | (0 << 1) | 1,
        MPU_KSTACK_LIMIT | (0 << 1) | 1);
    mpu_configure_region(5,
        MPU_APP_BASE | (0 << 3) | (1 << 1) | 0,   /* RW any, X */
        MPU_APP_LIMIT | (0 << 1) | 1);
#endif

    MPU_CTRL = (1 << 2) | 1;
    __asm volatile("dsb\nisb" ::: "memory");
    __asm volatile("cpsie i" ::: "memory");
}

static void mpu_restore_after_app(void) {
    __asm volatile("cpsid i" ::: "memory");
    MPU_CTRL = 0;
    __asm volatile("dsb\nisb" ::: "memory");

#ifdef BOARD_MPU_V7
    mpu_configure_region(1, MPU_RAM_RBAR, MPU_RAM_RASR_OPEN);
    mpu_configure_region(5, 0, 0);
#else
    mpu_configure_region(1,
        MPU_RAM_BASE | (0 << 3) | (1 << 1) | 0,
        MPU_RAM_LIMIT | (0 << 1) | 1);
    mpu_configure_region(4, 0, 0);
    mpu_configure_region(5, 0, 0);
#endif

    MPU_CTRL = (1 << 2) | 1;
    __asm volatile("dsb\nisb" ::: "memory");
    __asm volatile("cpsie i" ::: "memory");
}

/* ── Built-in apps (Thumb machine code) ──────────────────────── */
static const uint8_t hello_app[] = {
    0x48, 0x20, 0x00, 0xdf,  0x65, 0x20, 0x00, 0xdf,
    0x6c, 0x20, 0x00, 0xdf,  0x6c, 0x20, 0x00, 0xdf,
    0x6f, 0x20, 0x00, 0xdf,  0x20, 0x20, 0x00, 0xdf,
    0x66, 0x20, 0x00, 0xdf,  0x72, 0x20, 0x00, 0xdf,
    0x6f, 0x20, 0x00, 0xdf,  0x6d, 0x20, 0x00, 0xdf,
    0x20, 0x20, 0x00, 0xdf,  0x61, 0x20, 0x00, 0xdf,
    0x70, 0x20, 0x00, 0xdf,  0x70, 0x20, 0x00, 0xdf,
    0x21, 0x20, 0x00, 0xdf,  0x0d, 0x20, 0x00, 0xdf,
    0x0a, 0x20, 0x00, 0xdf,  0x70, 0x47,
};

static const uint8_t count_app[] = {
    0x31, 0x24, 0x20, 0x46, 0x00, 0xdf, 0x01, 0x34,
    0x36, 0x2c, 0xfa, 0xd1, 0x0d, 0x20, 0x00, 0xdf,
    0x0a, 0x20, 0x00, 0xdf, 0x70, 0x47,
};

static const uint8_t spin_app[] = { 0xfe, 0xe7 };

static const uint8_t rogue_app[] = {
    0x4f, 0xf0, 0x00, 0x00, 0xc0, 0xf2, 0x00, 0x00,
    0x01, 0x68, 0x70, 0x47,
};

static const uint8_t svc_hello_app[] = {
    0x48, 0x20, 0x00, 0xdf,  0x69, 0x20, 0x00, 0xdf,
    0x21, 0x20, 0x00, 0xdf,  0x0d, 0x20, 0x00, 0xdf,
    0x0a, 0x20, 0x00, 0xdf,  0x70, 0x47,
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
    "SimpleOS Lite " BOARD_VERSION " (hardened)\r\n"
    "Platform: " BOARD_NAME "\r\n"
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
    uart_putln("SimpleOS Lite " BOARD_VERSION " (hardened)");
#ifdef BOARD_MPU_V7
    uart_putln("  CPU:      ARM Cortex-M4 (ARMv7E-M)");
#else
    uart_putln("  CPU:      ARM Cortex-M33 (ARMv8-M Mainline)");
#endif
    uart_puts("  Platform: "); uart_putln(BOARD_NAME);
    uart_puts("  Flash:    0x"); write_hex32(BOARD_FLASH_BASE);
    uart_puts(" ("); write_dec(BOARD_FLASH_SIZE >> 10); uart_putln(" KB)");
    uart_puts("  RAM:      0x"); write_hex32(BOARD_RAM_BASE);
    uart_puts(" ("); write_dec(BOARD_RAM_SIZE >> 10); uart_putln(" KB)");
    uart_puts("  UART:     "); uart_putln(BOARD_UART_NAME);
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

static void __attribute__((naked, used)) app_exit_trampoline(void) {
    __asm volatile("svc #1\nb .\n");
}

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
    if (!(f->flags & 1)) { uart_putln("not executable"); return; }
    if (f->size > sizeof(app_region)) { uart_putln("binary too large"); return; }

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
    if (addr >= BOARD_FLASH_BASE && addr < BOARD_FLASH_BASE + BOARD_FLASH_SIZE) return 1;
    if (addr >= BOARD_RAM_BASE && addr < BOARD_RAM_BASE + BOARD_RAM_SIZE) return 1;
    if (addr >= 0x40000000 && addr < 0x60000000) return 1;
    if (addr >= 0xE000E000 && addr < 0xE0100000) return 1;
    return 0;
}

static void cmd_peek(const char *arg) {
    uint32_t addr = parse_hex(arg);
    if ((addr & 3) != 0) { uart_putln("error: address not 4-byte aligned"); return; }
    if (!addr_readable(addr)) { uart_putln("error: address not in readable region"); return; }
    uint32_t val = *(volatile uint32_t *)addr;
    uart_putc('['); write_hex32(addr); uart_puts("] = 0x"); write_hex32(val); uart_putln("");
}

static int addr_writable(uint32_t addr) {
    if (addr >= BOARD_RAM_BASE && addr < BOARD_RAM_BASE + BOARD_RAM_SIZE) return 1;
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
    if (!addr_writable(addr)) { uart_putln("error: address not in writable region"); return; }
    uint32_t val = parse_hex(p);
    *(volatile uint32_t *)addr = val;
    uart_putc('['); write_hex32(addr); uart_puts("] <- 0x"); write_hex32(val); uart_putln("");
}

static void cmd_mpu(void) {
    uart_puts("MPU_TYPE = 0x"); write_hex32(MPU_TYPE); uart_putln("");
    uart_puts("MPU_CTRL = 0x"); write_hex32(MPU_CTRL); uart_putln("");
    for (uint32_t i = 0; i < 8 && i < mpu_regions; i++) {
        MPU_RNR = i;
        uint32_t rbar = MPU_RBAR;
#ifdef BOARD_MPU_V7
        uint32_t rattr = MPU_RASR;
#else
        uint32_t rattr = MPU_RLAR;
#endif
        if (!(rattr & 1)) continue;
        uart_puts("  R"); write_dec(i);
        uart_puts(": RBAR=0x"); write_hex32(rbar);
#ifdef BOARD_MPU_V7
        uart_puts(" RASR=0x");
#else
        uart_puts(" RLAR=0x");
#endif
        write_hex32(rattr);
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
    write_dec(secs); uart_putc('.');
    if (ms < 100) uart_putc('0');
    if (ms < 10) uart_putc('0');
    write_dec(ms);
    uart_puts("s ("); write_dec(t); uart_putln(" ticks)");
}

static void cmd_stack(void) {
    uint32_t sp;
    uint32_t stack_top = (uint32_t)&_stack_top;
    __asm volatile("mov %0, sp" : "=r"(sp));
    uart_puts("  SP     = 0x"); write_hex32(sp); uart_putln("");
    uart_puts("  Top    = 0x"); write_hex32(stack_top); uart_putln("");
    uart_puts("  Used   = "); write_dec(stack_top - sp); uart_putln(" bytes");
    uart_puts("  Free   = "); write_dec(sp - (uint32_t)&_ebss); uart_putln(" bytes (to BSS end)");
    uint32_t canary_loc = ((uint32_t)&_ebss + 3) & ~3u;
    uint32_t canary_val = *(volatile uint32_t *)canary_loc;
    uart_puts("  Canary = 0x"); write_hex32(canary_val);
    if (canary_val == STACK_CANARY) uart_putln(" OK");
    else uart_putln(" CORRUPTED!");
}

static uint32_t flash_crc;

static uint32_t compute_flash_crc(void) {
    volatile uint32_t *p = (volatile uint32_t *)BOARD_FLASH_BASE;
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

static int cmd_selftest(void) {
    int pass = 0, fail = 0;

    uint32_t canary_loc = ((uint32_t)&_ebss + 3) & ~3u;
    uint32_t cv = *(volatile uint32_t *)canary_loc;
    uart_puts("  [1] Stack canary: ");
    if (cv == STACK_CANARY) { uart_putln("PASS"); pass++; } else { uart_putln("FAIL"); fail++; }

    uart_puts("  [2] Flash CRC:    ");
    uint32_t crc_now = compute_flash_crc();
    if (crc_now == flash_crc) { uart_putln("PASS"); pass++; } else { uart_putln("FAIL (modified!)"); fail++; }

    uart_puts("  [3] MPU enabled:  ");
    if (MPU_CTRL & 1) { uart_putln("PASS"); pass++; } else { uart_putln("FAIL"); fail++; }

    uart_puts("  [4] Faults on:    ");
    uint32_t sh = SCB_SHCSR;
    if ((sh & ((1<<16)|(1<<17)|(1<<18))) == ((1<<16)|(1<<17)|(1<<18))) {
        uart_putln("PASS"); pass++;
    } else { uart_putln("FAIL"); fail++; }

    uart_puts("  [5] DIV0 trap:    ");
    if (SCB_CCR & (1<<4)) { uart_putln("PASS"); pass++; } else { uart_putln("FAIL"); fail++; }

    uart_puts("  [6] SysTick:      ");
    if (tick_count > 0) { uart_putln("PASS"); pass++; } else { uart_putln("FAIL"); fail++; }

    uart_puts("  [7] XN enforce:   ");
    fault_expected = 1;
    fault_caught = 0;
    mpu_lockdown_for_app();
    try_fault_call((uint32_t)&_sbss | 1);
    mpu_restore_after_app();
    if (fault_caught & 0x01) { uart_putln("PASS"); pass++; }
    else { uart_putln("FAIL (XN not enforced)"); fail++; }

    uart_puts("  [8] AP-deny:      ");
    app_was_killed = 0;
    cmd_exec("rogue.bin");
    if (app_was_killed) { uart_putln("PASS"); pass++; }
    else { uart_putln("FAIL (kernel read not blocked)"); fail++; }

    uart_puts("  Result: ");
    write_dec(pass); uart_puts("/"); write_dec(pass + fail);
    uart_putln(fail ? " SOME FAILED" : " ALL PASSED");
    return fail;
}

#ifdef SIMPLEOS_QEMU_SMOKE
static void qemu_semihost_exit(int code) {
    static volatile uint32_t args[2];
    args[0] = 0x20026; /* ADP_Stopped_ApplicationExit */
    args[1] = (uint32_t)code;
    register uint32_t r0 __asm("r0") = 0x20; /* SYS_EXIT_EXTENDED */
    register uint32_t r1 __asm("r1") = (uint32_t)args;
    __asm volatile("bkpt 0xAB" : : "r"(r0), "r"(r1) : "memory");
    while (1) {}
}

static void qemu_smoke_run_and_exit(void) {
    uart_putln("[qemu-smoke] mode=boot-selftest");
    uint32_t spin = 0;
    __asm volatile("cpsie i" ::: "memory");
    while (tick_count == 0 && spin < 8u) {
        __asm volatile("wfi" ::: "memory");
        spin++;
    }
    int fail = cmd_selftest();
    if (fail == 0) {
        uart_putln("protection_probe=pass");
        uart_putln("protection_enabled=pass");
        uart_putln("region_contract=pass");
        uart_putln("fault_recovered=pass");
        uart_putln("[qemu-smoke] selftest=pass");
        uart_putln("TEST PASSED");
        qemu_semihost_exit(0);
    }
    uart_putln("[qemu-smoke] selftest=fail");
    uart_putln("TEST FAILED");
    qemu_semihost_exit(1);
}
#endif

/* ── Shell ────────────────────────────────────────────────────── */
static char shell_buf[128];
static int shell_pos;

static void shell(void) {
    uart_putln("SimpleOS Lite " BOARD_VERSION " (hardened)");
    uart_putln("Type 'help' for commands.");
    uart_putln("");
    uart_puts("simpleos> ");

    while (1) {
        while (!board_uart_rx_ready()) {}
        uint32_t ch = board_uart_getc();

        if (ch == '\r' || ch == '\n') {
            uart_putc('\r'); uart_putc('\n');
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
                else { uart_puts("unknown command: "); uart_putln(shell_buf); }
            }
            shell_pos = 0;
            uart_puts("simpleos> ");
            continue;
        }

        if (ch == 0x7F || ch == 0x08) {
            if (shell_pos > 0) {
                shell_pos--;
                uart_putc(0x08); uart_putc(' '); uart_putc(0x08);
            }
            continue;
        }

        if (shell_pos < 127) {
            shell_buf[shell_pos++] = (char)ch;
            board_uart_echo((char)ch);
        }
    }
}

/* ── Boot ─────────────────────────────────────────────────────── */

void Default_Handler(void) __attribute__((naked));
void Default_Handler(void) { __asm volatile("b ."); }

void Reset_Handler(void) __attribute__((naked, noreturn));

typedef void (*vector_fn)(void);

__attribute__((used, section(".vector_table"), aligned(512)))
const union { uint32_t w; vector_fn fn; } vectors[16] = {
    [0]  = { .w  = (uint32_t)&_stack_top },
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

void _c_main(void);

void Reset_Handler(void) {
    __asm volatile (
        "movw r0, :lower16:_stack_top\n"
        "movt r0, :upper16:_stack_top\n"
        "mov sp, r0\n"
        "bl _c_main\n"
        "b .\n"
    );
}

void _c_main(void) {
    uint32_t *p = &_sbss;
    while (p < &_ebss) *p++ = 0;

    p = &_app_sandbox_start;
    while (p < &_app_sandbox_end) *p++ = 0;

    SCB_VTOR = (uint32_t)vectors;

    uart_init();
    uart_putln("");
    uart_puts("[BOOT] SimpleOS Lite ");
    uart_puts(BOARD_VERSION);
    uart_putln(" - Cortex-M33 (ARMv8-M)");
    uart_puts("[BOOT] Platform: ");
    uart_putln(BOARD_NAME);
    uart_puts("[BOOT] UART initialized (");
    uart_puts(BOARD_UART_NAME);
    uart_putln(")");

    uint32_t canary_loc = ((uint32_t)&_ebss + 3) & ~3u;
    *(volatile uint32_t *)canary_loc = STACK_CANARY;

    faults_init();
    mpu_init();
    systick_init();
    fs_init();

    flash_crc = compute_flash_crc();
    uart_puts("[BOOT] Flash CRC: 0x"); write_hex32(flash_crc); uart_putln("");

    uint32_t cv = *(volatile uint32_t *)canary_loc;
    if (cv != STACK_CANARY) {
        uart_putln("[BOOT] WARNING: stack canary corrupt after init!");
    }

    uart_putln("[BOOT] Entering shell...");
    uart_putln("");

#ifdef SIMPLEOS_QEMU_SMOKE
    qemu_smoke_run_and_exit();
#endif

    shell();
}
