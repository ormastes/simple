# Serial Port Driver Specification

UART serial driver for bare-metal systems supporting:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BM-SERIAL-001 |
| Category | Bare-Metal / Drivers |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/feature/usage/serial_driver_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

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

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/serial_driver/result.json` |

## Scenarios

- COM1 is at 0x3F8
- COM2 is at 0x2F8
- COM3 is at 0x3E8
- COM4 is at 0x2E8
- DATA register at offset 0
- IER register at offset 1
- FCR/IIR register at offset 2
- LCR register at offset 3
- MCR register at offset 4
- LSR register at offset 5
- MSR register at offset 6
- Scratch register at offset 7
- DATA_READY is bit 0
- OVERRUN_ERR is bit 1
- PARITY_ERR is bit 2
- FRAMING_ERR is bit 3
- BREAK is bit 4
- THRE is bit 5
- TEMT is bit 6
- 115200 baud uses divisor 1
- 57600 baud uses divisor 2
- 38400 baud uses divisor 3
- 19200 baud uses divisor 6
- 9600 baud uses divisor 12
- divisor = 115200 / baud_rate
- DLAB is bit 7
- 8N1 configuration is 0x03
- 8 data bits is bits 0-1 set
- FIFO enable with 14-byte threshold is 0xC7
- FIFO enable bit is bit 0
- Clear RX FIFO is bit 1
- Clear TX FIFO is bit 2
- Normal operation mode is 0x0F
- Loopback mode is 0x1E
- DTR is bit 0
- RTS is bit 1
- LF byte is 0x0A
- CR byte is 0x0D
- LF converted to CR+LF for terminals
- test byte is 0xAE
