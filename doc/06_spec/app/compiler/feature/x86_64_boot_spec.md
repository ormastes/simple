# x86_64 Bare-Metal Boot Tests

**Feature ID:** #BAREMETAL-012 | **Category:** Baremetal | **Status:** In Progress

_Source: `test/feature/baremetal/x86_64_boot_spec.spl`_

---

## Overview

Tests x86_64 bare-metal boot functionality including 64-bit multiboot2 header generation
and validation, long mode setup through PAE (CR4), LME (EFER), and paging (CR0) control
register configuration, and 16-byte stack alignment verification. Validates that the x86_64
boot infrastructure correctly transitions from protected mode to long mode.

## Syntax

```simple
val header = multiboot2_header()
expect(header.magic).to_equal(0xE85250D6)
expect(validate_multiboot2(header)).to_equal(true)
expect(is_pae_enabled(CR4_PAE)).to_equal(true)
expect(is_long_mode_enabled(EFER_LME)).to_equal(true)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 4 |

## Test Structure

### x86_64 Boot Code

- ✅ generates valid 64-bit multiboot header
- ✅ validates multiboot2 header successfully
- ✅ sets up long mode correctly
- ✅ maintains 16-byte stack alignment
### x86_64 QEMU Boot

