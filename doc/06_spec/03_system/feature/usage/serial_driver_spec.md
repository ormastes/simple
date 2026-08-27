# Serial Port Driver Specification

> UART serial driver for bare-metal systems supporting:

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- COM1 is at 0x3F8
   - Expected: COM1 equals `0x3F8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("COM1 is at 0x3F8")
val COM1 = 0x3F8
expect(COM1).to_equal(0x3F8)
```

</details>

#### COM2 is at 0x2F8

- COM2 is at 0x2F8
   - Expected: COM2 equals `0x2F8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("COM2 is at 0x2F8")
val COM2 = 0x2F8
expect(COM2).to_equal(0x2F8)
```

</details>

#### COM3 is at 0x3E8

- COM3 is at 0x3E8
   - Expected: COM3 equals `0x3E8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("COM3 is at 0x3E8")
val COM3 = 0x3E8
expect(COM3).to_equal(0x3E8)
```

</details>

#### COM4 is at 0x2E8

- COM4 is at 0x2E8
   - Expected: COM4 equals `0x2E8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("COM4 is at 0x2E8")
val COM4 = 0x2E8
expect(COM4).to_equal(0x2E8)
```

</details>

### UART Register Offsets

#### DATA register at offset 0

- DATA register at offset 0
   - Expected: UART_DATA equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("DATA register at offset 0")
val UART_DATA = 0
expect(UART_DATA).to_equal(0)
```

</details>

#### IER register at offset 1

- IER register at offset 1
   - Expected: UART_IER equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("IER register at offset 1")
# Interrupt Enable Register.
val UART_IER = 1
expect(UART_IER).to_equal(1)
```

</details>

#### FCR/IIR register at offset 2

- FCR/IIR register at offset 2
   - Expected: UART_FCR equals `2`
   - Expected: UART_IIR equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("FCR/IIR register at offset 2")
# FIFO Control / Interrupt Identification.
val UART_FCR = 2
val UART_IIR = 2
expect(UART_FCR).to_equal(2)
expect(UART_IIR).to_equal(2)
```

</details>

#### LCR register at offset 3

- LCR register at offset 3
   - Expected: UART_LCR equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("LCR register at offset 3")
# Line Control Register.
val UART_LCR = 3
expect(UART_LCR).to_equal(3)
```

</details>

#### MCR register at offset 4

- MCR register at offset 4
   - Expected: UART_MCR equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("MCR register at offset 4")
# Modem Control Register.
val UART_MCR = 4
expect(UART_MCR).to_equal(4)
```

</details>

#### LSR register at offset 5

- LSR register at offset 5
   - Expected: UART_LSR equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("LSR register at offset 5")
# Line Status Register.
val UART_LSR = 5
expect(UART_LSR).to_equal(5)
```

</details>

#### MSR register at offset 6

- MSR register at offset 6
   - Expected: UART_MSR equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("MSR register at offset 6")
# Modem Status Register.
val UART_MSR = 6
expect(UART_MSR).to_equal(6)
```

</details>

#### Scratch register at offset 7

- Scratch register at offset 7
   - Expected: UART_SCRATCH equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Scratch register at offset 7")
val UART_SCRATCH = 7
expect(UART_SCRATCH).to_equal(7)
```

</details>

### Line Status Register Bits

#### DATA_READY is bit 0

- DATA_READY is bit 0
   - Expected: LSR_DATA_READY equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("DATA_READY is bit 0")
val LSR_DATA_READY = 1 << 0
expect(LSR_DATA_READY).to_equal(1)
```

</details>

#### OVERRUN_ERR is bit 1

- OVERRUN_ERR is bit 1
   - Expected: LSR_OVERRUN_ERR equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("OVERRUN_ERR is bit 1")
val LSR_OVERRUN_ERR = 1 << 1
expect(LSR_OVERRUN_ERR).to_equal(2)
```

</details>

#### PARITY_ERR is bit 2

- PARITY_ERR is bit 2
   - Expected: LSR_PARITY_ERR equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("PARITY_ERR is bit 2")
val LSR_PARITY_ERR = 1 << 2
expect(LSR_PARITY_ERR).to_equal(4)
```

</details>

#### FRAMING_ERR is bit 3

- FRAMING_ERR is bit 3
   - Expected: LSR_FRAMING_ERR equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("FRAMING_ERR is bit 3")
val LSR_FRAMING_ERR = 1 << 3
expect(LSR_FRAMING_ERR).to_equal(8)
```

</details>

#### BREAK is bit 4

- BREAK is bit 4
   - Expected: LSR_BREAK equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BREAK is bit 4")
val LSR_BREAK = 1 << 4
expect(LSR_BREAK).to_equal(16)
```

</details>

#### THRE is bit 5

- THRE is bit 5
   - Expected: LSR_THRE equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("THRE is bit 5")
# Transmit Holding Register Empty.
val LSR_THRE = 1 << 5
expect(LSR_THRE).to_equal(32)
```

</details>

#### TEMT is bit 6

- TEMT is bit 6
   - Expected: LSR_TEMT equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("TEMT is bit 6")
# Transmitter Empty.
val LSR_TEMT = 1 << 6
expect(LSR_TEMT).to_equal(64)
```

</details>

### Baud Rate Divisors

#### Standard baud rates

#### 115200 baud uses divisor 1

- 115200 baud uses divisor 1
   - Expected: BAUD_115200 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("115200 baud uses divisor 1")
val BAUD_115200 = 1
expect(BAUD_115200).to_equal(1)
```

</details>

#### 57600 baud uses divisor 2

- 57600 baud uses divisor 2
   - Expected: BAUD_57600 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("57600 baud uses divisor 2")
val BAUD_57600 = 2
expect(BAUD_57600).to_equal(2)
```

</details>

#### 38400 baud uses divisor 3

- 38400 baud uses divisor 3
   - Expected: BAUD_38400 equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("38400 baud uses divisor 3")
val BAUD_38400 = 3
expect(BAUD_38400).to_equal(3)
```

</details>

#### 19200 baud uses divisor 6

- 19200 baud uses divisor 6
   - Expected: BAUD_19200 equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("19200 baud uses divisor 6")
val BAUD_19200 = 6
expect(BAUD_19200).to_equal(6)
```

</details>

#### 9600 baud uses divisor 12

- 9600 baud uses divisor 12
   - Expected: BAUD_9600 equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("9600 baud uses divisor 12")
val BAUD_9600 = 12
expect(BAUD_9600).to_equal(12)
```

</details>

#### Divisor calculation

#### divisor = 115200 / baud_rate

- divisor = 115200 / baud_rate
   - Expected: divisor equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("divisor = 115200 / baud_rate")
# Base clock is 115200 Hz.
val BASE_CLOCK = 115200
val BAUD_RATE = 9600
val divisor = BASE_CLOCK / BAUD_RATE
expect(divisor).to_equal(12)
```

</details>

### Line Control Register

#### DLAB is bit 7

- DLAB is bit 7
   - Expected: LCR_DLAB equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("DLAB is bit 7")
# Divisor Latch Access Bit.
val LCR_DLAB = 1 << 7
expect(LCR_DLAB).to_equal(128)
```

</details>

#### 8N1 configuration is 0x03

- 8N1 configuration is 0x03
   - Expected: LCR_8N1 equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("8N1 configuration is 0x03")
# 8 data bits, no parity, 1 stop bit.
val LCR_8N1 = 0x03
expect(LCR_8N1).to_equal(3)
```

</details>

#### 8 data bits is bits 0-1 set

- 8 data bits is bits 0-1 set
   - Expected: WORD_LEN_8 equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("8 data bits is bits 0-1 set")
# Word length: 00=5, 01=6, 10=7, 11=8.
val WORD_LEN_8 = 0x03
expect(WORD_LEN_8).to_equal(3)
```

</details>

### FIFO Control

#### FIFO enable with 14-byte threshold is 0xC7

- FIFO enable with 14-byte threshold is 0xC7
   - Expected: FCR_CONFIG equals `199`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("FIFO enable with 14-byte threshold is 0xC7")
# Enable FIFO, clear TX/RX, 14-byte trigger.
val FCR_CONFIG = 0xC7
expect(FCR_CONFIG).to_equal(199)
```

</details>

#### FIFO enable bit is bit 0

- FIFO enable bit is bit 0
   - Expected: FCR_ENABLE equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("FIFO enable bit is bit 0")
val FCR_ENABLE = 1 << 0
expect(FCR_ENABLE).to_equal(1)
```

</details>

#### Clear RX FIFO is bit 1

- Clear RX FIFO is bit 1
   - Expected: FCR_CLEAR_RX equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Clear RX FIFO is bit 1")
val FCR_CLEAR_RX = 1 << 1
expect(FCR_CLEAR_RX).to_equal(2)
```

</details>

#### Clear TX FIFO is bit 2

- Clear TX FIFO is bit 2
   - Expected: FCR_CLEAR_TX equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Clear TX FIFO is bit 2")
val FCR_CLEAR_TX = 1 << 2
expect(FCR_CLEAR_TX).to_equal(4)
```

</details>

### Modem Control Register

#### Normal operation mode is 0x0F

- Normal operation mode is 0x0F
   - Expected: MCR_NORMAL equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Normal operation mode is 0x0F")
# RTS, DTR, OUT1, OUT2 all set.
val MCR_NORMAL = 0x0F
expect(MCR_NORMAL).to_equal(15)
```

</details>

<details>
<summary>Advanced: Loopback mode is 0x1E</summary>

#### Loopback mode is 0x1E

- Loopback mode is 0x1E
   - Expected: MCR_LOOPBACK equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Loopback mode is 0x1E")
# For self-test during initialization.
val MCR_LOOPBACK = 0x1E
expect(MCR_LOOPBACK).to_equal(30)
```

</details>


</details>

#### DTR is bit 0

- DTR is bit 0
   - Expected: MCR_DTR equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("DTR is bit 0")
val MCR_DTR = 1 << 0
expect(MCR_DTR).to_equal(1)
```

</details>

#### RTS is bit 1

- RTS is bit 1
   - Expected: MCR_RTS equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("RTS is bit 1")
val MCR_RTS = 1 << 1
expect(MCR_RTS).to_equal(2)
```

</details>

### Newline Handling

#### LF byte is 0x0A

- LF byte is 0x0A
   - Expected: LF equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("LF byte is 0x0A")
val LF = 0x0A
expect(LF).to_equal(10)
```

</details>

#### CR byte is 0x0D

- CR byte is 0x0D
   - Expected: CR equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("CR byte is 0x0D")
val CR = 0x0D
expect(CR).to_equal(13)
```

</details>

#### LF converted to CR+LF for terminals

- LF converted to CR+LF for terminals
   - Expected: expected_sequence[0] equals `13`
   - Expected: expected_sequence[1] equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("LF converted to CR+LF for terminals")
# Standard terminal newline sequence.
val expected_sequence = [0x0D, 0x0A]
expect(expected_sequence[0]).to_equal(13)
expect(expected_sequence[1]).to_equal(10)
```

</details>

### Test Byte for Loopback

#### test byte is 0xAE

- test byte is 0xAE
   - Expected: TEST_BYTE equals `174`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test byte is 0xAE")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `35e1b73db60d311347d07a0e869f2381a32674a7709dcb59ec679ef26e645b4f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `35e1b73db60d311347d07a0e869f2381a32674a7709dcb59ec679ef26e645b4f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `35e1b73db60d311347d07a0e869f2381a32674a7709dcb59ec679ef26e645b4f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/03_system/feature/usage/serial_driver_spec.spl
mirror: doc/06_spec/03_system/feature/usage/serial_driver_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=95 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/serial_driver_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/serial_driver_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/serial_driver_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 38 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/serial_driver_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'COM1 is at 0x3F8' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/serial_driver_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'COM2 is at 0x2F8' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/serial_driver_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'COM3 is at 0x3E8' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/serial_driver_spec.spl:325:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test byte is 0xAE' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
