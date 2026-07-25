/* Board: QEMU MPS2-AN505 (SSE-200 IoT Kit, Cortex-M33)
 * CMSDK APB UART0 at 0x40200000, 25 MHz system clock.
 * PMSAv8-M MPU (arbitrary regions, non-overlapping for QEMU bug).
 */
#ifndef BOARD_AN505_H
#define BOARD_AN505_H

#include <stdint.h>

#define BOARD_NAME       "MPS2-AN505 (QEMU)"
#define BOARD_UART_NAME  "CMSDK APB @ 0x40200000"
#define BOARD_VERSION    "v0.5"

#define BOARD_FLASH_BASE  0x10000000
#define BOARD_FLASH_SIZE  0x00400000
#define BOARD_RAM_BASE    0x20000000
#define BOARD_RAM_SIZE    0x00008000

#define BOARD_SYS_CLOCK      25000000
#define BOARD_SYSTICK_RELOAD (BOARD_SYS_CLOCK / 100 - 1)

/* PMSAv8-M MPU (non-overlapping for QEMU AN505 bug) */
#define MPU_FLASH_BASE       0x10000000
#define MPU_FLASH_LIMIT      0x103FFFE0
#define MPU_RAM_BASE         0x20000000
#define MPU_RAM_LIMIT        0x20007FE0
#define MPU_KDATA_LIMIT      0x20005FE0
#define MPU_APP_BASE         0x20006000
#define MPU_APP_LIMIT        0x200069E0
#define MPU_KSTACK_BASE      0x20006A00
#define MPU_KSTACK_LIMIT     0x20007FE0

#define BOARD_APP_REGION_SIZE 2048
#define BOARD_APP_STACK_SIZE  512

#define UART_BASE    0x40200000
#define UART_DATA    (*(volatile uint32_t *)(UART_BASE + 0x00))
#define UART_STATE   (*(volatile uint32_t *)(UART_BASE + 0x04))
#define UART_CTRL    (*(volatile uint32_t *)(UART_BASE + 0x08))
#define UART_BAUDDIV (*(volatile uint32_t *)(UART_BASE + 0x10))

static inline void board_clock_init(void) {}

static inline void board_uart_init(void) {
    UART_CTRL = 0x00;
    UART_BAUDDIV = 16;
    UART_CTRL = 0x03;
}

static inline void board_uart_putc(char c) {
    UART_DATA = (uint32_t)c;
}

static inline int board_uart_rx_ready(void) {
    return (UART_STATE & 2) != 0;
}

static inline uint32_t board_uart_getc(void) {
    return UART_DATA & 0xFF;
}

static inline void board_uart_echo(char c) {
    UART_DATA = (uint32_t)c;
}

#endif
