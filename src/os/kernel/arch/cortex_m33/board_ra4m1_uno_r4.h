/* Board: Arduino UNO R4 WiFi — Renesas RA4M1 (R7FA4M1AB, Cortex-M4)
 * SCI2 on P302(TXD)/P301(RXD) → ESP32-S3 USB bridge → host serial.
 * Default clock: MOCO 8 MHz; we switch to HOCO 48 MHz for UART accuracy.
 * PMSAv7 MPU (power-of-2 regions, overlapping priority).
 */
#ifndef BOARD_RA4M1_UNO_R4_H
#define BOARD_RA4M1_UNO_R4_H

#include <stdint.h>

#define BOARD_NAME       "Arduino UNO R4 WiFi"
#define BOARD_UART_NAME  "SCI2 @ 0x40070040"
#define BOARD_VERSION    "v0.5"
#define BOARD_MPU_V7

/* ── Memory map ─────────────────────────────────────────────── */
#define BOARD_FLASH_BASE  0x00000000
#define BOARD_FLASH_SIZE  0x00040000  /* 256 KB code flash */
#define BOARD_RAM_BASE    0x20000000
#define BOARD_RAM_SIZE    0x00008000  /* 32 KB SRAM */

/* System clock: HOCO 48 MHz (we switch from default MOCO 8 MHz) */
#define BOARD_SYS_CLOCK      48000000
#define BOARD_SYSTICK_RELOAD (BOARD_SYS_CLOCK / 100 - 1)  /* 100 Hz */

/* ── MPU partition (PMSAv7, power-of-2 aligned) ─────────────── *
 * Real Cortex-M4 handles overlapping regions correctly via priority,
 * so we use Region 1 (full RAM, priv-only during lockdown) overlapped
 * by Region 5 (app sandbox, RW all) which wins by higher number.
 *
 *   0x20000000 – 0x20005FFF  Kernel data  (24K, covered by Region 1)
 *   0x20006000 – 0x20006FFF  App sandbox  (4K, Region 5 during exec)
 *   0x20007000 – 0x20007FFF  Kernel stack (4K, covered by Region 1)
 */
#define BOARD_APP_REGION_SIZE 2048
#define BOARD_APP_STACK_SIZE  512

/* PMSAv7 RASR: XN[28] | AP[26:24] | TEX[21:19] | S[18] | C[17] | B[16]
 *              | SRD[15:8] | SIZE[4:1] | EN[0]
 * Normal WB-WA: TEX=000, C=1, B=1, S=1 */
#define RASR_NORMAL_WB(ap, xn, sz) \
    (((xn)<<28) | ((ap)<<24) | (1u<<18) | (1u<<17) | (1u<<16) | ((sz)<<1) | 1u)
#define RASR_DEVICE(ap, xn, sz) \
    (((xn)<<28) | ((ap)<<24) | (1u<<16) | ((sz)<<1) | 1u)

/* Region 0: Flash 256KB — RO+X, Normal */
#define MPU_FLASH_RBAR   0x00000000
#define MPU_FLASH_RASR   RASR_NORMAL_WB(6, 0, 17)  /* AP=110 RO all, SIZE=17(256K) */

/* Region 1: RAM 32KB — initial: RW all+X; lockdown: priv-only+XN */
#define MPU_RAM_RBAR     0x20000000
#define MPU_RAM_RASR_OPEN   RASR_NORMAL_WB(3, 0, 14)  /* AP=011 RW all, SIZE=14(32K) */
#define MPU_RAM_RASR_LOCKED RASR_NORMAL_WB(1, 1, 14)  /* AP=001 priv-only, XN, SIZE=14(32K) */

/* Region 2: Peripherals 0x40000000 512MB — priv-only+XN, Device */
#define MPU_PERIPH_RBAR  0x40000000
#define MPU_PERIPH_RASR  RASR_DEVICE(1, 1, 28)  /* SIZE=28(512M) */

/* Region 3: PPB 0xE0000000 1MB — priv-only+XN, Device */
#define MPU_PPB_RBAR     0xE0000000
#define MPU_PPB_RASR     RASR_DEVICE(1, 1, 19)  /* SIZE=19(1M) */

/* Region 5: App sandbox 4KB — RW all+X, Normal (overrides Region 1 by priority) */
#define MPU_APP_BASE     0x20006000
#define MPU_APP_RASR     RASR_NORMAL_WB(3, 0, 11)  /* AP=011 RW all, SIZE=11(4K) */

/* ── System Protection ──────────────────────────────────────── */
#define SYSTEM_PRCR   (*(volatile uint16_t *)0x4001E3FE)
#define PRCR_KEY      0xA500u
#define PRCR_PRC0     (1u << 0)  /* Clock registers */
#define PRCR_PRC1     (1u << 1)  /* Module stop / low power */

/* ── Clock ──────────────────────────────────────────────────── */
#define SYSTEM_SCKSCR (*(volatile uint8_t *)0x4001E026)
#define SYSTEM_HOCOCR (*(volatile uint8_t *)0x4001E036)
#define SYSTEM_OSCSF  (*(volatile uint8_t *)0x4001E03C)

/* ── Module Stop ────────────────────────────────────────────── */
#define MSTPCRB       (*(volatile uint32_t *)0x40047004)

/* ── Pin Function ───────────────────────────────────────────── */
#define PWPR          (*(volatile uint8_t *)0x40040D03)
#define PFS_BASE      0x40040800u
#define P301_PFS      (*(volatile uint32_t *)(PFS_BASE + 0x64))  /* port3 pin1 */
#define P302_PFS      (*(volatile uint32_t *)(PFS_BASE + 0x68))  /* port3 pin2 */

/* ── SCI2 ───────────────────────────────────────────────────── */
#define SCI2_BASE     0x40070040u
#define SCI2_SMR      (*(volatile uint8_t *)(SCI2_BASE + 0x00))
#define SCI2_BRR      (*(volatile uint8_t *)(SCI2_BASE + 0x01))
#define SCI2_SCR      (*(volatile uint8_t *)(SCI2_BASE + 0x02))
#define SCI2_TDR      (*(volatile uint8_t *)(SCI2_BASE + 0x03))
#define SCI2_SSR      (*(volatile uint8_t *)(SCI2_BASE + 0x04))
#define SCI2_RDR      (*(volatile uint8_t *)(SCI2_BASE + 0x05))
#define SCI2_SEMR     (*(volatile uint8_t *)(SCI2_BASE + 0x07))

static inline void board_clock_init(void) {
    /* Switch system clock from MOCO (8 MHz) to HOCO (48 MHz) */
    SYSTEM_PRCR = PRCR_KEY | PRCR_PRC0;
    SYSTEM_HOCOCR = 0x00;  /* HOCO run (may already be running after reset) */
    while (!(SYSTEM_OSCSF & 0x01)) {}  /* Wait HOCO stable */
    SYSTEM_SCKSCR = 0x00;  /* Select HOCO */
    SYSTEM_PRCR = PRCR_KEY;

    /* Enable SCI2 module (clear MSTP bit 29) */
    SYSTEM_PRCR = PRCR_KEY | PRCR_PRC1;
    MSTPCRB &= ~(1u << 29);
    SYSTEM_PRCR = PRCR_KEY;
}

static inline void board_uart_init(void) {
    /* Unlock PFS write protect */
    PWPR = 0x00;  /* Clear B0WI */
    PWPR = 0x40;  /* Set PFSWE */

    /* P302 = TXD2 (SCI2, PSEL=4, output) */
    P302_PFS = (1u << 16) | (4u << 24) | (1u << 2);  /* PMR | PSEL=4 | PDR */
    /* P301 = RXD2 (SCI2, PSEL=4, input) */
    P301_PFS = (1u << 16) | (4u << 24);  /* PMR | PSEL=4 */

    /* Lock PFS */
    PWPR = 0x00;  /* Clear PFSWE */
    PWPR = 0x80;  /* Set B0WI */

    /* Configure SCI2: 115200 baud, 8N1, async */
    SCI2_SCR  = 0x00;   /* Disable TX/RX first */
    SCI2_SMR  = 0x00;   /* Async, 8N1, PCLKA/1 (n=0) */
    SCI2_SEMR = 0x10;   /* ABCS=1 (8 base clocks/bit) → divisor=32 */
    SCI2_BRR  = 12;     /* 48MHz / (32 × 13) = 115384 baud (0.16% error) */
    /* Wait for BRR stabilization (~1 bit period at 48 MHz) */
    for (volatile int d = 0; d < 500; d++) {}
    SCI2_SCR  = 0x30;   /* TE=1, RE=1 */
}

static inline void board_uart_putc(char c) {
    while (!(SCI2_SSR & (1 << 7))) {}  /* TDRE */
    SCI2_TDR = (uint8_t)c;
}

static inline int board_uart_rx_ready(void) {
    return (SCI2_SSR & (1 << 6)) != 0;  /* RDRF */
}

static inline uint32_t board_uart_getc(void) {
    uint8_t c = SCI2_RDR;
    SCI2_SSR &= ~(1 << 6);  /* Clear RDRF */
    return c;
}

static inline void board_uart_echo(char c) {
    board_uart_putc(c);
}

#endif /* BOARD_RA4M1_UNO_R4_H */
