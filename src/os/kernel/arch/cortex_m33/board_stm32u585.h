/* Board: STM32U585 (Arduino Uno Q) — TZEN=0, non-secure boot
 * Console: LPUART1 on PG7(TX)/PG8(RX) AF8. On the Uno Q this is the
 * MCU<->MPU link, which the Qualcomm side exposes as /dev/ttyHS1 at
 * 115200 (arduino-router). USART1 (PB6/PB7) goes to header pins D1/D0
 * and reaches nothing observable. PG[15:2] live in the VDDIO2 domain, so
 * PWR_SVMCR.IO2SV must be set before the GPIOG mux takes effect.
 * Default clock: MSIS 4 MHz, all prescalers 1x (PCLK3 = 4 MHz).
 * PMSAv8-M MPU.
 */
#ifndef BOARD_STM32U585_H
#define BOARD_STM32U585_H

#include <stdint.h>

#define BOARD_NAME       "STM32U585 (Arduino Uno Q)"
#define BOARD_UART_NAME  "LPUART1 @ 0x46002400"
#define BOARD_VERSION    "v0.5"

#define BOARD_FLASH_BASE  0x08000000
#define BOARD_FLASH_SIZE  0x00200000
#define BOARD_RAM_BASE    0x20000000
#define BOARD_RAM_SIZE    0x000C0000

#define BOARD_SYS_CLOCK      4000000
#define BOARD_SYSTICK_RELOAD (BOARD_SYS_CLOCK / 100 - 1)

/* PMSAv8-M MPU (non-overlapping, 768KB layout) */
#define MPU_FLASH_BASE       0x08000000
#define MPU_FLASH_LIMIT      0x081FFFE0
#define MPU_RAM_BASE         0x20000000
#define MPU_RAM_LIMIT        0x200BFFE0
#define MPU_KDATA_LIMIT      0x2003FFE0
#define MPU_APP_BASE         0x20040000
#define MPU_APP_LIMIT        0x2005FFE0
#define MPU_KSTACK_BASE      0x20060000
#define MPU_KSTACK_LIMIT     0x200BFFE0

#define BOARD_APP_REGION_SIZE 65536
#define BOARD_APP_STACK_SIZE  8192

#define RCC_BASE      0x46020C00
#define RCC_AHB2ENR1  (*(volatile uint32_t *)(RCC_BASE + 0x8C))
#define RCC_AHB3ENR   (*(volatile uint32_t *)(RCC_BASE + 0x94))
#define RCC_APB3ENR   (*(volatile uint32_t *)(RCC_BASE + 0xA8))

#define PWR_BASE      0x46020800
#define PWR_SVMCR     (*(volatile uint32_t *)(PWR_BASE + 0x10))

#define GPIOG_BASE    0x42021800
#define GPIOG_MODER   (*(volatile uint32_t *)(GPIOG_BASE + 0x00))
#define GPIOG_AFRL    (*(volatile uint32_t *)(GPIOG_BASE + 0x20))
#define GPIOG_AFRH    (*(volatile uint32_t *)(GPIOG_BASE + 0x24))

#define LPUART1_BASE  0x46002400
#define LPUART1_CR1   (*(volatile uint32_t *)(LPUART1_BASE + 0x00))
#define LPUART1_BRR   (*(volatile uint32_t *)(LPUART1_BASE + 0x0C))
#define LPUART1_ISR   (*(volatile uint32_t *)(LPUART1_BASE + 0x1C))
#define LPUART1_RDR   (*(volatile uint32_t *)(LPUART1_BASE + 0x24))
#define LPUART1_TDR   (*(volatile uint32_t *)(LPUART1_BASE + 0x28))

/* LPUART baud = 256 * fck / BRR; fck = PCLK3 = 4 MHz -> 115200 */
#define LPUART1_BRR_115200 8889

static inline void board_clock_init(void) {
    RCC_AHB3ENR  |= (1 << 2);   /* PWREN */
    RCC_AHB2ENR1 |= (1 << 6);   /* GPIOGEN */
    RCC_APB3ENR  |= (1 << 6);   /* LPUART1EN */
    volatile uint32_t dummy = RCC_APB3ENR;
    (void)dummy;
    PWR_SVMCR |= (1u << 29);    /* IO2SV: VDDIO2 valid, enables PG[15:2] */
}

static inline void board_uart_init(void) {
    uint32_t moder = GPIOG_MODER;
    moder &= ~((3u << 14) | (3u << 16));
    moder |=  ((2u << 14) | (2u << 16));
    GPIOG_MODER = moder;
    GPIOG_AFRL = (GPIOG_AFRL & ~(0xFu << 28)) | (8u << 28);  /* PG7 AF8 TX */
    GPIOG_AFRH = (GPIOG_AFRH & ~(0xFu << 0))  | (8u << 0);   /* PG8 AF8 RX */
    LPUART1_CR1 = 0;
    LPUART1_BRR = LPUART1_BRR_115200;
    LPUART1_CR1 = (1 << 3) | (1 << 2) | (1 << 0);
}

static inline void board_uart_putc(char c) {
    while (!(LPUART1_ISR & (1 << 7))) {}
    LPUART1_TDR = (uint32_t)c;
}

static inline int board_uart_rx_ready(void) {
    return (LPUART1_ISR & (1 << 5)) != 0;
}

static inline uint32_t board_uart_getc(void) {
    return LPUART1_RDR & 0xFF;
}

static inline void board_uart_echo(char c) {
    board_uart_putc(c);
}

#endif
