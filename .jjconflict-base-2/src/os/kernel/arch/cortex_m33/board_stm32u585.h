/* Board: STM32U585 (Arduino Uno Q) — TZEN=0, non-secure boot
 * USART1 on PA9(TX)/PA10(RX) AF7 via ST-LINK VCP.
 * Default clock: MSIS 4 MHz, all prescalers 1x.
 * PMSAv8-M MPU.
 */
#ifndef BOARD_STM32U585_H
#define BOARD_STM32U585_H

#include <stdint.h>

#define BOARD_NAME       "STM32U585 (Arduino Uno Q)"
#define BOARD_UART_NAME  "USART1 @ 0x40013800"
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
#define RCC_APB2ENR   (*(volatile uint32_t *)(RCC_BASE + 0xA4))

#define GPIOA_BASE    0x42020000
#define GPIOA_MODER   (*(volatile uint32_t *)(GPIOA_BASE + 0x00))
#define GPIOA_AFRH    (*(volatile uint32_t *)(GPIOA_BASE + 0x24))

#define USART1_BASE   0x40013800
#define USART1_CR1    (*(volatile uint32_t *)(USART1_BASE + 0x00))
#define USART1_BRR    (*(volatile uint32_t *)(USART1_BASE + 0x0C))
#define USART1_ISR    (*(volatile uint32_t *)(USART1_BASE + 0x1C))
#define USART1_RDR    (*(volatile uint32_t *)(USART1_BASE + 0x24))
#define USART1_TDR    (*(volatile uint32_t *)(USART1_BASE + 0x28))

static inline void board_clock_init(void) {
    RCC_AHB2ENR1 |= (1 << 0);
    RCC_APB2ENR  |= (1 << 14);
    volatile uint32_t dummy = RCC_APB2ENR;
    (void)dummy;
}

static inline void board_uart_init(void) {
    uint32_t moder = GPIOA_MODER;
    moder &= ~((3u << 18) | (3u << 20));
    moder |=  ((2u << 18) | (2u << 20));
    GPIOA_MODER = moder;
    uint32_t afrh = GPIOA_AFRH;
    afrh &= ~((0xFu << 4) | (0xFu << 8));
    afrh |=  ((7u   << 4) | (7u   << 8));
    GPIOA_AFRH = afrh;
    USART1_CR1 = 0;
    USART1_BRR = 35;
    USART1_CR1 = (1 << 3) | (1 << 2) | (1 << 0);
}

static inline void board_uart_putc(char c) {
    while (!(USART1_ISR & (1 << 7))) {}
    USART1_TDR = (uint32_t)c;
}

static inline int board_uart_rx_ready(void) {
    return (USART1_ISR & (1 << 5)) != 0;
}

static inline uint32_t board_uart_getc(void) {
    return USART1_RDR & 0xFF;
}

static inline void board_uart_echo(char c) {
    board_uart_putc(c);
}

#endif
