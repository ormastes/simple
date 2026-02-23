# x86 Bare-Metal Boot Tests

**Feature ID:** #BAREMETAL-013 | **Category:** Baremetal | **Status:** In Progress

_Source: `test/feature/baremetal/x86_boot_spec.spl`_

---

## Overview

Tests x86 bare-metal boot functionality including multiboot header generation with correct
magic number (0x1BADB002), flags, and checksum validation. Verifies boot code allocates a
64KB stack with 16-byte alignment and sets up the stack pointer correctly. Also includes
skipped tests for linker script placement and QEMU boot verification.

## Syntax

```simple
val header = multiboot_header()
expect(header.magic).to_equal(0x1BADB002)
expect(validate_multiboot(header)).to_equal(true)
expect(STACK_SIZE).to_equal(65536)
val sp = get_stack_pointer()
expect(sp % 16).to_equal(0)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 7 |

## Test Structure

### x86 Multiboot Header

- ✅ has correct magic number
- ✅ has valid checksum
- ✅ has correct flags
- ✅ validates successfully
### x86 Boot Code

- ✅ allocates 64KB stack
- ✅ maintains 16-byte stack alignment
- ✅ sets up stack pointer correctly
### x86 Linker Script

### x86 QEMU Boot

