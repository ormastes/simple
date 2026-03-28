# RISC-V 64-bit Bare-Metal Boot Tests

**Feature ID:** #BAREMETAL-009 | **Category:** Baremetal | **Status:** In Progress

_Source: `test/feature/baremetal/riscv64_boot_spec.spl`_

---

## Overview

Tests RISC-V 64-bit bare-metal boot functionality including machine mode startup,
trap vector setup with direct and vectored modes, machine status register initialization,
interrupt enable configuration (timer, external, software), and 16-byte stack alignment.
Validates that the RISC-V 64 boot infrastructure correctly initializes mtvec, mstatus, and mie CSRs.

## Syntax

```simple
val mstatus = MSTATUS_MPP_MACHINE
expect(check_machine_mode(mstatus)).to_equal(true)

val mtvec = 0x80000100
val (base, mode) = parse_mtvec(mtvec)
expect(mode).to_equal(MTVEC_MODE_DIRECT)
expect(validate_trap_vector(mtvec)).to_equal(true)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 3 |

## Test Structure

### RISC-V 64 Boot Code

- ✅ starts in machine mode
- ✅ sets up trap vector
- ✅ configures machine registers
### RISC-V 64 QEMU Boot

