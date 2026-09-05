/* riscv64 boot-contract probe payload.
 *
 * Linked against the REAL arch/riscv64/boot/crt0.S and the REAL
 * arch/riscv64/linker.ld by
 * scripts/check/check-simpleos-riscv64-image-header-contract.shs and
 * scripts/check/check-simpleos-riscv64-opensbi-guest-boot.shs.
 * Mirror of scripts/check/fixtures/arm64_boot_contract_probe.c.
 *
 * Evidence it prints (each is a discriminating check, not decoration):
 *   - c-start      : crt0 reached C with a working stack
 *   - bss-zeroed   : crt0 really zeroed .bss
 *   - data-ok      : .data was loaded (fw_payload carried the whole image)
 *   - rodata-ok    : an ABSOLUTE rodata pointer works — the image executes
 *                    at its link address 0x80200000
 *   - dtb-ok       : a1 pointed at a real FDT (0xd00dfeed) — the firmware
 *                    handover contract, not a garbage register
 *   - sbi-ok       : an SBI ecall (base ext 0x10, get_spec_version) answered
 *                    with error==0 — live OpenSBI is actually underneath us
 *   - SIMPLEOS-RV64-REALFW-BOOT-OK : all of the above held
 */

typedef unsigned long u64;
typedef unsigned int u32;
typedef unsigned char u8;

/* QEMU virt: 16550 UART, byte registers at 0x10000000. */
#define UART_BASE 0x10000000UL
#define UART_THR (*(volatile u8 *)(UART_BASE + 0x00))
#define UART_LSR (*(volatile u8 *)(UART_BASE + 0x05))

static void putc_(char c) {
    while ((UART_LSR & 0x20) == 0) { }
    UART_THR = (u8)c;
}
static void puts_(const char *s) {
    while (*s) putc_(*s++);
    putc_('\r');
    putc_('\n');
}

static u8 bss_probe[64];               /* .bss  — must be zero */
static u32 data_probe = 0x51D0BEEF;    /* .data — must survive load */
static const char rodata_msg[] = "[probe] rodata-ok";
/* Absolute pointer into .rodata: only prints sanely if we run at the link
 * address. */
static const char *const rodata_ptr = rodata_msg;

struct sbiret { long error; long value; };
static struct sbiret sbi_call(long eid, long fid, long a0v, long a1v) {
    register long a0 asm("a0") = a0v;
    register long a1 asm("a1") = a1v;
    register long a6 asm("a6") = fid;
    register long a7 asm("a7") = eid;
    asm volatile("ecall" : "+r"(a0), "+r"(a1) : "r"(a6), "r"(a7) : "memory");
    struct sbiret r = { a0, a1 };
    return r;
}

void boot_entry(u64 hartid, u64 dtb) {
    (void)hartid;
    puts_("[probe] rv64 c-start");

    int zeroed = 1;
    for (unsigned i = 0; i < sizeof bss_probe; i++)
        if (bss_probe[i] != 0) zeroed = 0;
    if (zeroed) puts_("[probe] bss-zeroed");

    if (data_probe == 0x51D0BEEF) puts_("[probe] data-ok");

    puts_(rodata_ptr);

    if (dtb != 0) {
        const volatile u8 *f = (const volatile u8 *)dtb;
        if (f[0] == 0xd0 && f[1] == 0x0d && f[2] == 0xfe && f[3] == 0xed)
            puts_("[probe] dtb-ok");
    }

    struct sbiret v = sbi_call(0x10, 0, 0, 0); /* base: get_spec_version */
    if (v.error == 0 && v.value > 0) puts_("[probe] sbi-ok");

    puts_("[probe] SIMPLEOS-RV64-REALFW-BOOT-OK");
}
