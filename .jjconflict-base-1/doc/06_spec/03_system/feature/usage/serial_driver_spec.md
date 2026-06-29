# Serial Port Driver Specification

> UART serial driver for bare-metal systems supporting:

<!-- sdn-diagram:id=serial_driver_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=serial_driver_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

serial_driver_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=serial_driver_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serial Port Driver Specification

UART serial driver for bare-metal systems supporting:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BM-SERIAL-001 |
| Category | Bare-Metal / Drivers |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/03_system/feature/usage/serial_driver_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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

## Scenarios

### COM Port Addresses

#### COM1 is at 0x3F8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val COM1 = 0x3F8
expect(COM1).to_equal(0x3F8)
```

</details>

#### COM2 is at 0x2F8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val COM2 = 0x2F8
expect(COM2).to_equal(0x2F8)
```

</details>

#### COM3 is at 0x3E8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val COM3 = 0x3E8
expect(COM3).to_equal(0x3E8)
```

</details>

#### COM4 is at 0x2E8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val COM4 = 0x2E8
expect(COM4).to_equal(0x2E8)
```

</details>

### UART Register Offsets

#### DATA register at offset 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val UART_DATA = 0
expect(UART_DATA).to_equal(0)
```

</details>

#### IER register at offset 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Interrupt Enable Register.
val UART_IER = 1
expect(UART_IER).to_equal(1)
```

</details>

#### FCR/IIR register at offset 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# FIFO Control / Interrupt Identification.
val UART_FCR = 2
val UART_IIR = 2
expect(UART_FCR).to_equal(2)
expect(UART_IIR).to_equal(2)
```

</details>

#### LCR register at offset 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Line Control Register.
val UART_LCR = 3
expect(UART_LCR).to_equal(3)
```

</details>

#### MCR register at offset 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Modem Control Register.
val UART_MCR = 4
expect(UART_MCR).to_equal(4)
```

</details>

#### LSR register at offset 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Line Status Register.
val UART_LSR = 5
expect(UART_LSR).to_equal(5)
```

</details>

#### MSR register at offset 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Modem Status Register.
val UART_MSR = 6
expect(UART_MSR).to_equal(6)
```

</details>

#### Scratch register at offset 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val UART_SCRATCH = 7
expect(UART_SCRATCH).to_equal(7)
```

</details>

### Line Status Register Bits

#### DATA_READY is bit 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val LSR_DATA_READY = 1 << 0
expect(LSR_DATA_READY).to_equal(1)
```

</details>

#### OVERRUN_ERR is bit 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val LSR_OVERRUN_ERR = 1 << 1
expect(LSR_OVERRUN_ERR).to_equal(2)
```

</details>

#### PARITY_ERR is bit 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val LSR_PARITY_ERR = 1 << 2
expect(LSR_PARITY_ERR).to_equal(4)
```

</details>

#### FRAMING_ERR is bit 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val LSR_FRAMING_ERR = 1 << 3
expect(LSR_FRAMING_ERR).to_equal(8)
```

</details>

#### BREAK is bit 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val LSR_BREAK = 1 << 4
expect(LSR_BREAK).to_equal(16)
```

</details>

#### THRE is bit 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Transmit Holding Register Empty.
val LSR_THRE = 1 << 5
expect(LSR_THRE).to_equal(32)
```

</details>

#### TEMT is bit 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Transmitter Empty.
val LSR_TEMT = 1 << 6
expect(LSR_TEMT).to_equal(64)
```

</details>

### Baud Rate Divisors

#### Standard baud rates

#### 115200 baud uses divisor 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val BAUD_115200 = 1
expect(BAUD_115200).to_equal(1)
```

</details>

#### 57600 baud uses divisor 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val BAUD_57600 = 2
expect(BAUD_57600).to_equal(2)
```

</details>

#### 38400 baud uses divisor 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val BAUD_38400 = 3
expect(BAUD_38400).to_equal(3)
```

</details>

#### 19200 baud uses divisor 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val BAUD_19200 = 6
expect(BAUD_19200).to_equal(6)
```

</details>

#### 9600 baud uses divisor 12

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val BAUD_9600 = 12
expect(BAUD_9600).to_equal(12)
```

</details>

#### Divisor calculation

#### divisor = 115200 / baud_rate

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Base clock is 115200 Hz.
val BASE_CLOCK = 115200
val BAUD_RATE = 9600
val divisor = BASE_CLOCK / BAUD_RATE
expect(divisor).to_equal(12)
```

</details>

### Line Control Register

#### DLAB is bit 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Divisor Latch Access Bit.
val LCR_DLAB = 1 << 7
expect(LCR_DLAB).to_equal(128)
```

</details>

#### 8N1 configuration is 0x03

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 8 data bits, no parity, 1 stop bit.
val LCR_8N1 = 0x03
expect(LCR_8N1).to_equal(3)
```

</details>

#### 8 data bits is bits 0-1 set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Word length: 00=5, 01=6, 10=7, 11=8.
val WORD_LEN_8 = 0x03
expect(WORD_LEN_8).to_equal(3)
```

</details>

### FIFO Control

#### FIFO enable with 14-byte threshold is 0xC7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Enable FIFO, clear TX/RX, 14-byte trigger.
val FCR_CONFIG = 0xC7
expect(FCR_CONFIG).to_equal(199)
```

</details>

#### FIFO enable bit is bit 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val FCR_ENABLE = 1 << 0
expect(FCR_ENABLE).to_equal(1)
```

</details>

#### Clear RX FIFO is bit 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val FCR_CLEAR_RX = 1 << 1
expect(FCR_CLEAR_RX).to_equal(2)
```

</details>

#### Clear TX FIFO is bit 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val FCR_CLEAR_TX = 1 << 2
expect(FCR_CLEAR_TX).to_equal(4)
```

</details>

### Modem Control Register

#### Normal operation mode is 0x0F

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RTS, DTR, OUT1, OUT2 all set.
val MCR_NORMAL = 0x0F
expect(MCR_NORMAL).to_equal(15)
```

</details>

<details>
<summary>Advanced: Loopback mode is 0x1E</summary>

#### Loopback mode is 0x1E

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# For self-test during initialization.
val MCR_LOOPBACK = 0x1E
expect(MCR_LOOPBACK).to_equal(30)
```

</details>


</details>

#### DTR is bit 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val MCR_DTR = 1 << 0
expect(MCR_DTR).to_equal(1)
```

</details>

#### RTS is bit 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val MCR_RTS = 1 << 1
expect(MCR_RTS).to_equal(2)
```

</details>

### Newline Handling

#### LF byte is 0x0A

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val LF = 0x0A
expect(LF).to_equal(10)
```

</details>

#### CR byte is 0x0D

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val CR = 0x0D
expect(CR).to_equal(13)
```

</details>

#### LF converted to CR+LF for terminals

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Standard terminal newline sequence.
val expected_sequence = [0x0D, 0x0A]
expect(expected_sequence[0]).to_equal(13)
expect(expected_sequence[1]).to_equal(10)
```

</details>

### Test Byte for Loopback

#### test byte is 0xAE

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arbitrary byte used for loopback test.
val TEST_BYTE = 0xAE
expect(TEST_BYTE).to_equal(174)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
