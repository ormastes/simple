# Bare-Metal Syscall and Peripheral Tests

**Feature ID:** #BAREMETAL-011 | **Category:** Baremetal | **Status:** In Progress

_Source: `test/feature/baremetal/syscall_spec.spl`_

---

## Overview

Tests bare-metal syscall wrappers including semihosting operations (debug console output,
file I/O, timing), UART configuration and byte transmission, timer initialization and delay
functions, and memory-mapped I/O register access with bit manipulation. All tests operate
on hardware register addresses and verify peripheral interaction patterns.

## Syntax

```simple
semi_write_string("Test message\n")
uart_init(0x40011000, 115200)
uart_write_byte(0x40011000, 65)
timer_delay_ms(0x40000000, 10)
mem_write_u32(0x40020000, 0x12345678)
mem_set_bit(0x40020000, 5)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 20 |

## Test Structure

### Semihosting

#### basic operations

- ✅ writes string to debug console
- ✅ exits with status code
#### file I/O

- ✅ opens file for reading
- ✅ writes to file
#### timing

- ✅ reads clock in centiseconds
### UART

#### initialization

- ✅ configures UART with baud rate
#### byte transmission

- ✅ writes single byte
- ✅ writes string
#### status checking

- ✅ checks if UART ready to write
- ✅ checks if data available to read
### Timer

#### initialization

- ✅ configures timer frequency
#### counter access

- ✅ reads current counter value
#### delays

- ✅ delays for milliseconds
- ✅ delays for microseconds
### Memory-Mapped I/O

#### register access

- ✅ reads and writes 32-bit registers
- ✅ reads and writes 8-bit registers
#### bit manipulation

- ✅ sets specific bit
- ✅ clears specific bit
- ✅ tests specific bit
- ✅ modifies bits with mask

