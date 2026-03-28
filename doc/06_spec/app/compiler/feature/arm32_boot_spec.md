# ARM32 (Cortex-M) Bare-Metal Boot Tests

**Feature ID:** #BAREMETAL-002 | **Category:** Baremetal | **Status:** In Progress

_Source: `test/feature/baremetal/arm32_boot_spec.spl`_

---

## Overview

Tests ARM Cortex-M bare-metal boot functionality including vector table generation,
reset handler behavior, stack pointer initialization, and NVIC interrupt controller setup.
Validates that the ARM32 boot infrastructure correctly places exception vectors, initializes
.data and .bss sections, and maintains AAPCS stack alignment.

## Syntax

```simple
val vt = create_vector_table()
expect(vt.initial_sp).to_equal(STACK_TOP)
expect(check_vector_alignment(0x08000000)).to_equal(true)
expect(check_data_init(0x20000000, 0x20001000)).to_equal(true)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 7 |

## Test Structure

### ARM32 Vector Table

- ✅ generates valid vector table
- ✅ has correct exception count
- ✅ places vector table at aligned address
- ✅ has zero reserved entries
### ARM32 Reset Handler

- ✅ initializes .data section
- ✅ zeros .bss section
- ✅ sets up stack pointer
### ARM32 NVIC (Nested Vectored Interrupt Controller)

### ARM32 QEMU Boot

