# RISC-V 32 Semihosting Tests

**Feature ID:** #BAREMETAL-006 | **Category:** Baremetal | **Status:** Active

_Source: `test/feature/baremetal/hello_riscv32_semihost_spec.spl`_

---

## Overview

Tests RISC-V 32-bit semihosting functionality by running actual ELF binaries on QEMU
with semihosting enabled. Validates hello world output, semihost test markers, exit codes,
and an intensive C test suite of 89 hardware tests covering 32-bit arithmetic, mcycle
counter reading, QEMU platform detection, interrupt cause bits, and stack alignment.

## Syntax

```simple
fn run_qemu(elf_path: text, timeout_ms: i64) -> (text, text, i32):
    var args: [text] = ["-M", "virt", "-bios", "none", "-kernel", elf_path,
        "-nographic", "-semihosting-config", "enable=on,target=native"]
    rt_process_run_timeout(QEMU_BIN, args, timeout_ms)

val output = run_qemu_output(BINARY_PATH, 10000)
expect(output).to_contain("Hello, RISC-V 32!")
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 11 |

## Test Structure

### RISC-V 32 Semihosting - Hello World

- ✅ prints hello world message
- ✅ outputs semihost test success marker
- ✅ outputs exit code 0 message
- ✅ completes within 5 seconds
### RISC-V 32 Semihosting - Intensive C Test

- ✅ runs 89 hardware tests on QEMU
- ✅ verifies semihosting operations
- ✅ verifies 32-bit arithmetic on real RV32
- ✅ verifies mcycle counter reading
- ✅ verifies QEMU platform (RV32, M-mode, little-endian)
- ✅ verifies interrupt cause bits are RV32 (bit 31)
- ✅ verifies stack alignment on real hardware

