# Inline Assembly Integration Tests

**Feature ID:** #BAREMETAL-007 | **Category:** Baremetal | **Status:** Active

_Source: `test/feature/baremetal/inline_asm_integration_spec.spl`_

---

## Overview

End-to-end tests for inline assembly in bare-metal contexts across x86, ARM, and RISC-V
architectures. Covers port I/O operations, CPU control instructions (CLI/STI/HLT), control
register access, MMIO register operations, semihosting calls, spinlock implementations,
cache operations, atomic instructions (CAS, increment, exchange), context switching, and
timer counter reading (TSC/RDTSCP).

## Syntax

```simple
fn serial_write_byte(byte: u8):
    val COM1_PORT: u16 = 0x3F8
    unsafe:
        asm volatile("out dx, al", in("dx") COM1_PORT, in("al") byte)

fn atomic_cas(ptr: *mut u32, expected: u32, desired: u32) -> bool:
    unsafe:
        asm volatile("lock cmpxchg [{ptr}], {desired}",
            ptr = in(reg) ptr, desired = in(reg) desired,
            inout("eax") expected => old)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 31 |

## Test Structure

### x86 Port I/O Operations

- ✅ implements outb for serial port

