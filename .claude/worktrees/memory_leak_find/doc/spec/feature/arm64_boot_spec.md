# ARM64 (AArch64) Bare-Metal Boot Tests

**Feature ID:** #BAREMETAL-003 | **Category:** Baremetal | **Status:** In Progress

_Source: `test/feature/baremetal/arm64_boot_spec.spl`_

---

## Overview

Tests ARM64 (AArch64) bare-metal boot functionality including exception vector table
generation, exception level (EL0-EL3) setup and transitions, VBAR alignment validation,
and 16-byte stack pointer alignment. Verifies the ARM64 boot infrastructure handles
EL transitions correctly and maintains AArch64 calling convention requirements.

## Syntax

```simple
val vt = create_vector_table()
expect(vt.sync_current_sp0.handler > 0).to_equal(true)
expect(check_vbar_alignment(0x40000000)).to_equal(true)
expect(check_el_transition(EL3, EL1)).to_equal(true)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 4 |

## Test Structure

### ARM64 Boot Code

- ✅ generates valid exception vector table
- ✅ checks vector table alignment
- ✅ sets up exception levels correctly
- ✅ maintains stack pointer alignment
### ARM64 QEMU Boot

