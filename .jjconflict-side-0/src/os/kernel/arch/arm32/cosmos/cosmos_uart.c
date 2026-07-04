/* CRZ Cosmos+ OpenSSD (Zynq-7000) Cadence UART driver + bring-up main.
 *
 * Zynq-7000 has two Cadence UARTs: UART0 @ 0xE0000000, UART1 @ 0xE0001000.
 * qemu's xilinx-zynq-a9 routes the first -serial to UART1; we drive both so the
 * banner appears regardless of which the host wired. Polled TX only (no IRQ, no
 * baud reprogram — qemu's model accepts TX without reconfiguring the divisor).
 */

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

static void cadence_uart_init(unsigned int base) {
    volatile unsigned int *cr = (volatile unsigned int *)(base + UART_CR);
    volatile unsigned int *mr = (volatile unsigned int *)(base + UART_MR);
    *cr = UART_CR_RXRST | UART_CR_TXRST;   /* reset FIFOs */
    *mr = UART_MR_8N1;
    *cr = UART_CR_TXEN | UART_CR_RXEN;      /* enable TX/RX (clears the reset-default TXDIS) */
}

/* Exported so a Simple boot entry can drive the same UART (cf. rt_riscv_uart_put). */
void rt_cadence_uart_put(unsigned int byte) {
    /* UART1 is the qemu-zynq default serial; mirror to UART0 too. */
    volatile unsigned int *sr1 = (volatile unsigned int *)(CADENCE_UART1 + UART_SR);
    volatile unsigned int *fifo1 = (volatile unsigned int *)(CADENCE_UART1 + UART_FIFO);
    while (*sr1 & UART_SR_TXFULL) { }
    *fifo1 = byte & 0xFF;
    volatile unsigned int *sr0 = (volatile unsigned int *)(CADENCE_UART0 + UART_SR);
    volatile unsigned int *fifo0 = (volatile unsigned int *)(CADENCE_UART0 + UART_FIFO);
    while (*sr0 & UART_SR_TXFULL) { }
    *fifo0 = byte & 0xFF;
}

static void cosmos_puts(const char *s) {
    for (; *s; s++) {
        rt_cadence_uart_put((unsigned int)(unsigned char)*s);
    }
}

void cosmos_boot_main(void) {
    cadence_uart_init(CADENCE_UART0);
    cadence_uart_init(CADENCE_UART1);
    cosmos_puts("COSMOS+ OpenSSD (Zynq-7000 / Cortex-A9) boot OK\r\n");
    cosmos_puts("[cosmos] Cadence UART1@0xE0001000 up; DDR/OCM mapped\r\n");
    cosmos_puts("[cosmos] NVMe-fw seams present: FMC register model (fil_fmc), HIL host queue\r\n");
    cosmos_puts("[cosmos] MISSING for silicon: Zynq NFC PL binding, PCIe endpoint, DDR/OCM init, A9 SMP/GIC, FSBL handoff\r\n");
    for (;;) {
        __asm__ volatile("wfi");
    }
}
