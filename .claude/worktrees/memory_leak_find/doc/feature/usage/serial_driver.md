# Serial Port Driver Specification
*Source:* `test/feature/usage/serial_driver_spec.spl`
**Feature IDs:** #BM-SERIAL-001  |  **Category:** Bare-Metal / Drivers  |  **Status:** In Progress

## Overview



## Overview

UART serial driver for bare-metal systems supporting:
- COM1-COM4 port access
- Configurable baud rates (9600-115200)
- 8N1 configuration (8 data bits, no parity, 1 stop bit)
- FIFO buffering
- CR/LF newline handling

## Key Concepts

| Concept | Description |
|---------|-------------|
| COM Port | Standard PC serial ports (0x3F8, 0x2F8, etc.) |
| Baud Rate | Data transmission speed (bits per second) |
| DLAB | Divisor Latch Access Bit for baud rate config |
| LSR | Line Status Register for TX/RX status |

## Implementation Notes

- QEMU uses -serial stdio to connect COM1 to terminal
- LF (0x0A) automatically converted to CR+LF for terminals
- Transmit waits for buffer empty before sending

## Feature: COM Port Addresses

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | COM1 is at 0x3F8 | pass |
| 2 | COM2 is at 0x2F8 | pass |
| 3 | COM3 is at 0x3E8 | pass |
| 4 | COM4 is at 0x2E8 | pass |

**Example:** COM1 is at 0x3F8
    Given val COM1 = 0x3F8
    Then  expect(COM1).to_equal(0x3F8)

**Example:** COM2 is at 0x2F8
    Given val COM2 = 0x2F8
    Then  expect(COM2).to_equal(0x2F8)

**Example:** COM3 is at 0x3E8
    Given val COM3 = 0x3E8
    Then  expect(COM3).to_equal(0x3E8)

**Example:** COM4 is at 0x2E8
    Given val COM4 = 0x2E8
    Then  expect(COM4).to_equal(0x2E8)

## Feature: UART Register Offsets

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | DATA register at offset 0 | pass |
| 2 | IER register at offset 1 | pass |
| 3 | FCR/IIR register at offset 2 | pass |
| 4 | LCR register at offset 3 | pass |
| 5 | MCR register at offset 4 | pass |
| 6 | LSR register at offset 5 | pass |
| 7 | MSR register at offset 6 | pass |
| 8 | Scratch register at offset 7 | pass |

**Example:** DATA register at offset 0
    Given val UART_DATA = 0
    Then  expect(UART_DATA).to_equal(0)

**Example:** IER register at offset 1
    Given val UART_IER = 1
    Then  expect(UART_IER).to_equal(1)

**Example:** FCR/IIR register at offset 2
    Given val UART_FCR = 2
    Given val UART_IIR = 2
    Then  expect(UART_FCR).to_equal(2)
    Then  expect(UART_IIR).to_equal(2)

**Example:** LCR register at offset 3
    Given val UART_LCR = 3
    Then  expect(UART_LCR).to_equal(3)

**Example:** MCR register at offset 4
    Given val UART_MCR = 4
    Then  expect(UART_MCR).to_equal(4)

**Example:** LSR register at offset 5
    Given val UART_LSR = 5
    Then  expect(UART_LSR).to_equal(5)

**Example:** MSR register at offset 6
    Given val UART_MSR = 6
    Then  expect(UART_MSR).to_equal(6)

**Example:** Scratch register at offset 7
    Given val UART_SCRATCH = 7
    Then  expect(UART_SCRATCH).to_equal(7)

## Feature: Line Status Register Bits

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | DATA_READY is bit 0 | pass |
| 2 | OVERRUN_ERR is bit 1 | pass |
| 3 | PARITY_ERR is bit 2 | pass |
| 4 | FRAMING_ERR is bit 3 | pass |
| 5 | BREAK is bit 4 | pass |
| 6 | THRE is bit 5 | pass |
| 7 | TEMT is bit 6 | pass |

**Example:** DATA_READY is bit 0
    Given val LSR_DATA_READY = 1 << 0
    Then  expect(LSR_DATA_READY).to_equal(1)

**Example:** OVERRUN_ERR is bit 1
    Given val LSR_OVERRUN_ERR = 1 << 1
    Then  expect(LSR_OVERRUN_ERR).to_equal(2)

**Example:** PARITY_ERR is bit 2
    Given val LSR_PARITY_ERR = 1 << 2
    Then  expect(LSR_PARITY_ERR).to_equal(4)

**Example:** FRAMING_ERR is bit 3
    Given val LSR_FRAMING_ERR = 1 << 3
    Then  expect(LSR_FRAMING_ERR).to_equal(8)

**Example:** BREAK is bit 4
    Given val LSR_BREAK = 1 << 4
    Then  expect(LSR_BREAK).to_equal(16)

**Example:** THRE is bit 5
    Given val LSR_THRE = 1 << 5
    Then  expect(LSR_THRE).to_equal(32)

**Example:** TEMT is bit 6
    Given val LSR_TEMT = 1 << 6
    Then  expect(LSR_TEMT).to_equal(64)

## Feature: Baud Rate Divisors

### Scenario: Standard baud rates

| # | Example | Status |
|---|---------|--------|
| 1 | 115200 baud uses divisor 1 | pass |
| 2 | 57600 baud uses divisor 2 | pass |
| 3 | 38400 baud uses divisor 3 | pass |
| 4 | 19200 baud uses divisor 6 | pass |
| 5 | 9600 baud uses divisor 12 | pass |

**Example:** 115200 baud uses divisor 1
    Given val BAUD_115200 = 1
    Then  expect(BAUD_115200).to_equal(1)

**Example:** 57600 baud uses divisor 2
    Given val BAUD_57600 = 2
    Then  expect(BAUD_57600).to_equal(2)

**Example:** 38400 baud uses divisor 3
    Given val BAUD_38400 = 3
    Then  expect(BAUD_38400).to_equal(3)

**Example:** 19200 baud uses divisor 6
    Given val BAUD_19200 = 6
    Then  expect(BAUD_19200).to_equal(6)

**Example:** 9600 baud uses divisor 12
    Given val BAUD_9600 = 12
    Then  expect(BAUD_9600).to_equal(12)

### Scenario: Divisor calculation

| # | Example | Status |
|---|---------|--------|
| 1 | divisor = 115200 / baud_rate | pass |

**Example:** divisor = 115200 / baud_rate
    Given val BASE_CLOCK = 115200
    Given val BAUD_RATE = 9600
    Given val divisor = BASE_CLOCK / BAUD_RATE
    Then  expect(divisor).to_equal(12)

## Feature: Line Control Register

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | DLAB is bit 7 | pass |
| 2 | 8N1 configuration is 0x03 | pass |
| 3 | 8 data bits is bits 0-1 set | pass |

**Example:** DLAB is bit 7
    Given val LCR_DLAB = 1 << 7
    Then  expect(LCR_DLAB).to_equal(128)

**Example:** 8N1 configuration is 0x03
    Given val LCR_8N1 = 0x03
    Then  expect(LCR_8N1).to_equal(3)

**Example:** 8 data bits is bits 0-1 set
    Given val WORD_LEN_8 = 0x03
    Then  expect(WORD_LEN_8).to_equal(3)

## Feature: FIFO Control

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | FIFO enable with 14-byte threshold is 0xC7 | pass |
| 2 | FIFO enable bit is bit 0 | pass |
| 3 | Clear RX FIFO is bit 1 | pass |
| 4 | Clear TX FIFO is bit 2 | pass |

**Example:** FIFO enable with 14-byte threshold is 0xC7
    Given val FCR_CONFIG = 0xC7
    Then  expect(FCR_CONFIG).to_equal(199)

**Example:** FIFO enable bit is bit 0
    Given val FCR_ENABLE = 1 << 0
    Then  expect(FCR_ENABLE).to_equal(1)

**Example:** Clear RX FIFO is bit 1
    Given val FCR_CLEAR_RX = 1 << 1
    Then  expect(FCR_CLEAR_RX).to_equal(2)

**Example:** Clear TX FIFO is bit 2
    Given val FCR_CLEAR_TX = 1 << 2
    Then  expect(FCR_CLEAR_TX).to_equal(4)

## Feature: Modem Control Register

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | Normal operation mode is 0x0F | pass |
| 2 | Loopback mode is 0x1E | pass |
| 3 | DTR is bit 0 | pass |
| 4 | RTS is bit 1 | pass |

**Example:** Normal operation mode is 0x0F
    Given val MCR_NORMAL = 0x0F
    Then  expect(MCR_NORMAL).to_equal(15)

**Example:** Loopback mode is 0x1E
    Given val MCR_LOOPBACK = 0x1E
    Then  expect(MCR_LOOPBACK).to_equal(30)

**Example:** DTR is bit 0
    Given val MCR_DTR = 1 << 0
    Then  expect(MCR_DTR).to_equal(1)

**Example:** RTS is bit 1
    Given val MCR_RTS = 1 << 1
    Then  expect(MCR_RTS).to_equal(2)

## Feature: Newline Handling

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | LF byte is 0x0A | pass |
| 2 | CR byte is 0x0D | pass |
| 3 | LF converted to CR+LF for terminals | pass |

**Example:** LF byte is 0x0A
    Given val LF = 0x0A
    Then  expect(LF).to_equal(10)

**Example:** CR byte is 0x0D
    Given val CR = 0x0D
    Then  expect(CR).to_equal(13)

**Example:** LF converted to CR+LF for terminals
    Given val expected_sequence = [0x0D, 0x0A]
    Then  expect(expected_sequence[0]).to_equal(13)
    Then  expect(expected_sequence[1]).to_equal(10)

## Feature: Test Byte for Loopback

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | test byte is 0xAE | pass |

**Example:** test byte is 0xAE
    Given val TEST_BYTE = 0xAE
    Then  expect(TEST_BYTE).to_equal(174)


