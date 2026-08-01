/* CRZ Cosmos+ OpenSSD (Zynq-7000) Cadence UART driver + bring-up main.
 *
 * Zynq-7000 has two Cadence UARTs: UART0 @ 0xE0000000, UART1 @ 0xE0001000.
 * qemu's xilinx-zynq-a9 routes the first -serial to UART1; we drive both so the
 * banner appears regardless of which the host wired. Polled TX only (no IRQ, no
 * baud reprogram — qemu's model accepts TX without reconfiguring the divisor).
 */

#include "cosmos_hal.h"
#include "cosmos_storage.h"

extern void cosmos_irq_enable(void);

#if COSMOS_IS_QEMU
#if defined(COSMOS_PROFILE_OPENSSD2_8CH8WAY_V300) || \
    defined(COSMOS_NFC_PACKAGE_VERIFIED_OPENSSD2_8C8W_3_0_0) || \
    defined(COSMOS_PCIE_BITSTREAM_CONTRACT)
#error "QEMU must remain unbound from Cosmos+ silicon contracts"
#endif
#else
#if !defined(COSMOS_PROFILE_OPENSSD2_8CH8WAY_V300) || \
    !defined(COSMOS_NFC_PACKAGE_VERIFIED_OPENSSD2_8C8W_3_0_0) || \
    !defined(COSMOS_NFC_DMA_IDENTITY_BASE) || \
    !defined(COSMOS_NFC_DMA_IDENTITY_END) || \
    !defined(COSMOS_NFC_TOGGLE_PAYLOAD_ADDRESS) || \
    !defined(COSMOS_PCIE_BITSTREAM_CONTRACT)
#error "Silicon builds require the exact Cosmos+ 8Ch8Way v3.0.0 profile"
#endif
#if COSMOS_PROFILE_OPENSSD2_8CH8WAY_V300 != 1 || \
    COSMOS_NFC_PACKAGE_VERIFIED_OPENSSD2_8C8W_3_0_0 != 1 || \
    COSMOS_NFC_DMA_IDENTITY_BASE != 0x00200000U || \
    COSMOS_NFC_DMA_IDENTITY_END != 0x17FFFFFFU || \
    COSMOS_NFC_TOGGLE_PAYLOAD_ADDRESS != 0x17000D00U || \
    COSMOS_PCIE_BITSTREAM_CONTRACT != 0x030000U
#error "Cosmos+ silicon contract does not match official 8Ch8Way v3.0.0"
#endif

#define COSMOS_STRINGIFY_INNER(value) #value
#define COSMOS_STRINGIFY(value) COSMOS_STRINGIFY_INNER(value)

__asm__(
    ".section .note.cosmos.profile,\"a\",%note\n"
    ".balign 4\n"
    ".global " COSMOS_STRINGIFY(COSMOS_PROFILE_ELF_SYMBOL) "\n"
    ".type " COSMOS_STRINGIFY(COSMOS_PROFILE_ELF_SYMBOL) ",%object\n"
    COSMOS_STRINGIFY(COSMOS_PROFILE_ELF_SYMBOL) ":\n"
    ".long 7\n"
    ".long .Lcosmos_profile_desc_end-.Lcosmos_profile_desc_start\n"
    ".long " COSMOS_STRINGIFY(COSMOS_PROFILE_NOTE_TYPE) "\n"
    ".asciz " COSMOS_STRINGIFY(COSMOS_PROFILE_NOTE_NAME) "\n"
    ".balign 4\n"
    ".Lcosmos_profile_desc_start:\n"
    ".asciz " COSMOS_STRINGIFY(COSMOS_PROFILE_NOTE_DESCRIPTOR) "\n"
    ".Lcosmos_profile_desc_end:\n"
    ".balign 4\n"
    ".size " COSMOS_STRINGIFY(COSMOS_PROFILE_ELF_SYMBOL) ",.-"
        COSMOS_STRINGIFY(COSMOS_PROFILE_ELF_SYMBOL) "\n"
    ".previous\n");
#endif

#define CADENCE_UART0 0xE0000000U
#define CADENCE_UART1 0xE0001000U
#define UART_CR       0x00U    /* control register */
#define UART_MR       0x04U    /* mode register */
#define UART_SR       0x2CU    /* channel status register */
#define UART_FIFO     0x30U    /* TX/RX FIFO */
#define UART_SR_TXFULL (1U << 4)
#define UART_CR_RXRST  (1U << 0)
#define UART_CR_TXRST  (1U << 1)
#define UART_CR_RXEN   (1U << 2)
#define UART_CR_TXEN   (1U << 4)
#define UART_MR_8N1    0x20U    /* 8 data bits, no parity, 1 stop */
#define UART0_ENABLED  (1U << 0)
#define UART1_ENABLED  (1U << 1)
#define UART_NOT_READY 0x55415230U
#define UART_READY     0x55415254U
#define EXCEPTION_CLEAR 0x434C4541U
#define EXCEPTION_ACTIVE 0x41435449U

static unsigned int cadence_uart_enabled = UART0_ENABLED | UART1_ENABLED;
static volatile unsigned int cosmos_uart_state = UART_NOT_READY;

volatile unsigned int cosmos_exception_active = EXCEPTION_CLEAR;
volatile unsigned int cosmos_exception_kind;
volatile unsigned int cosmos_exception_status;
volatile unsigned int cosmos_exception_address;
volatile unsigned int cosmos_exception_pc;

static void cadence_uart_init(unsigned int base) {
    volatile unsigned int *cr = (volatile unsigned int *)(base + UART_CR);
    volatile unsigned int *mr = (volatile unsigned int *)(base + UART_MR);
    *cr = UART_CR_RXRST | UART_CR_TXRST;   /* reset FIFOs */
    *mr = UART_MR_8N1;
    *cr = UART_CR_TXEN | UART_CR_RXEN;      /* enable TX/RX (clears the reset-default TXDIS) */
}

static int cadence_uart_try_put(unsigned int base, unsigned int byte) {
    unsigned int poll;
    volatile unsigned int *sr = (volatile unsigned int *)(base + UART_SR);
    volatile unsigned int *fifo = (volatile unsigned int *)(base + UART_FIFO);

    for (poll = 0U; poll < COSMOS_POLL_LIMIT; poll++) {
        if ((*sr & UART_SR_TXFULL) == 0U) {
            *fifo = byte & 0xFFU;
            return COSMOS_OK;
        }
    }
    return COSMOS_TIMEOUT;
}

/* Exported so a Simple boot entry can drive the same UART (cf. rt_riscv_uart_put). */
void rt_cadence_uart_put(unsigned int byte) {
    /* UART1 is the qemu-zynq default serial; mirror to UART0 while each is responsive. */
    if ((cadence_uart_enabled & UART1_ENABLED) != 0U &&
        cadence_uart_try_put(CADENCE_UART1, byte) != COSMOS_OK) {
        cadence_uart_enabled &= ~UART1_ENABLED;
    }
    if ((cadence_uart_enabled & UART0_ENABLED) != 0U &&
        cadence_uart_try_put(CADENCE_UART0, byte) != COSMOS_OK) {
        cadence_uart_enabled &= ~UART0_ENABLED;
    }
}

static void cosmos_puts(const char *s) {
    for (; *s; s++) {
        rt_cadence_uart_put((unsigned int)(unsigned char)*s);
    }
}

__attribute__((noreturn))
void cosmos_exception_halt(
    unsigned int kind,
    unsigned int status,
    unsigned int address,
    unsigned int pc) {
    if (cosmos_exception_active == EXCEPTION_CLEAR) {
        cosmos_exception_active = EXCEPTION_ACTIVE;
        cosmos_exception_kind = kind;
        cosmos_exception_status = status;
        cosmos_exception_address = address;
        cosmos_exception_pc = pc;
        cosmos_data_sync_barrier();
        if (cosmos_uart_state == UART_READY) {
            cosmos_puts(kind == 1U
                ? "[cosmos] PREFETCH ABORT\r\n"
                : "[cosmos] DATA ABORT\r\n");
        }
    }
    __asm__ volatile("cpsid if" ::: "memory");
    for (;;) {
        __asm__ volatile("wfi");
    }
}

static const char *cosmos_status_name(int status) {
    switch (status) {
        case COSMOS_OK: return "OK";
        case COSMOS_UNAVAILABLE: return "UNAVAILABLE";
        case COSMOS_INVALID: return "INVALID";
        case COSMOS_TIMEOUT: return "TIMEOUT";
        case COSMOS_HW_ERROR: return "HW_ERROR";
        default: return "UNKNOWN";
    }
}

static void cosmos_report_status(const char *name, int status) {
    cosmos_puts("[cosmos] ");
    cosmos_puts(name);
    cosmos_puts(": ");
    cosmos_puts(cosmos_status_name(status));
    cosmos_puts("\r\n");
}

static int cosmos_handoff_allows_devices(int software_ok, int fsbl_status) {
    return software_ok && (COSMOS_IS_QEMU || fsbl_status == COSMOS_OK);
}

static int cosmos_boot_policy_selftest(void) {
    return !cosmos_handoff_allows_devices(0, COSMOS_OK) &&
#if COSMOS_IS_QEMU
        cosmos_handoff_allows_devices(1, COSMOS_UNAVAILABLE);
#else
        cosmos_handoff_allows_devices(1, COSMOS_OK) &&
        !cosmos_handoff_allows_devices(1, COSMOS_UNAVAILABLE);
#endif
}

static unsigned char cosmos_secondary_stack[4096] __attribute__((aligned(16)));

static void cosmos_secondary_main(void) {
    for (;;) {
        __asm__ volatile("wfi");
    }
}

void cosmos_boot_main(void) {
    int runtime_status;
    int mmu_status = COSMOS_UNAVAILABLE;
    int gic_status = COSMOS_UNAVAILABLE;
    int smp_status = COSMOS_UNAVAILABLE;
    int nfc_status = COSMOS_UNAVAILABLE;
    int pcie_status = COSMOS_UNAVAILABLE;
    int storage_status = COSMOS_UNAVAILABLE;
    int fsbl_status = COSMOS_UNAVAILABLE;
    int software_ok;

    cadence_uart_init(CADENCE_UART0);
    cadence_uart_init(CADENCE_UART1);
    cosmos_uart_state = UART_READY;
    cosmos_puts("COSMOS+ OpenSSD (Zynq-7000 / Cortex-A9) boot OK\r\n");

    cosmos_runtime_init();
    runtime_status = cosmos_runtime_selftest();
    if (runtime_status == COSMOS_OK) {
        mmu_status = cosmos_mmu_cache_selftest();
        if (mmu_status == COSMOS_OK) {
            mmu_status = cosmos_mmu_cache_init();
        }
    }
    if (mmu_status == COSMOS_OK) {
        gic_status = cosmos_gic_init_primary();
        if (gic_status == COSMOS_OK) {
            gic_status = cosmos_smp_selftest();
        }
    }

    software_ok = runtime_status == COSMOS_OK &&
        mmu_status == COSMOS_OK &&
        gic_status == COSMOS_OK &&
        cosmos_boot_policy_selftest();
    if (software_ok) {
        fsbl_status = cosmos_fsbl_selftest();
        if (fsbl_status == COSMOS_OK) {
            fsbl_status = cosmos_fsbl_validate_handoff();
        }
    }
    if (cosmos_handoff_allows_devices(software_ok, fsbl_status)) {
        nfc_status = cosmos_nfc_selftest();
        if (nfc_status == COSMOS_OK) {
            nfc_status = cosmos_nfc_init();
        }
        pcie_status = cosmos_pcie_selftest();
        if (pcie_status == COSMOS_OK) {
            pcie_status = cosmos_pcie_init();
        }
        if (nfc_status == COSMOS_OK && pcie_status == COSMOS_OK) {
            storage_status = cosmos_storage_init();
        }

        if (!COSMOS_IS_QEMU) {
            smp_status = cosmos_smp_release_secondary(
                (unsigned int)cosmos_secondary_main,
                (unsigned int)(cosmos_secondary_stack + sizeof(cosmos_secondary_stack)));
        }
    }

    cosmos_report_status("ARMv7 runtime", runtime_status);
    cosmos_report_status("MMU/L1/PL310", mmu_status);
    cosmos_report_status("GIC primary", gic_status);
    cosmos_report_status("CPU1 release", smp_status);
    cosmos_report_status("FSBL handoff", fsbl_status);
    cosmos_report_status("NFC PL", nfc_status);
    cosmos_report_status("PCIe PL", pcie_status);
    cosmos_report_status("NVMe storage", storage_status);

    if (COSMOS_IS_QEMU) {
        if (software_ok &&
            smp_status == COSMOS_UNAVAILABLE &&
            fsbl_status == COSMOS_UNAVAILABLE &&
            nfc_status == COSMOS_UNAVAILABLE &&
            pcie_status == COSMOS_UNAVAILABLE &&
            storage_status == COSMOS_UNAVAILABLE) {
            cosmos_puts("COSMOS SOFTWARE HAL CHECKS PASS\r\n");
            cosmos_puts("COSMOS SILICON VALIDATION PENDING\r\n");
        } else {
            cosmos_puts("COSMOS SOFTWARE HAL CHECKS FAIL\r\n");
        }
    } else {
        if (software_ok &&
            smp_status == COSMOS_OK &&
            fsbl_status == COSMOS_OK &&
            nfc_status == COSMOS_OK &&
            pcie_status == COSMOS_OK &&
            storage_status == COSMOS_OK) {
            cosmos_puts("COSMOS SILICON HAL CHECKS PASS\r\n");
        } else {
            cosmos_puts("COSMOS SILICON HAL CHECKS FAIL\r\n");
        }
    }
    if (gic_status == COSMOS_OK) {
        cosmos_irq_enable();
    }
    for (;;) {
        if (storage_status == COSMOS_OK) {
            int status = cosmos_storage_poll();

            if (status == COSMOS_OK || status == COSMOS_RETRY) {
                continue;
            }
            storage_status = status;
            cosmos_report_status("NVMe storage runtime", storage_status);
        }
        __asm__ volatile("wfi");
    }
}
