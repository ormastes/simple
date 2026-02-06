# Semihosting Testing - Quick Start Guide

**Version:** 0.5.0
**Date:** 2026-02-06
**Status:** Phase 1 Complete

---

## Overview

Test bare-metal RISC-V programs using **semihosting** and **SSpec** test framework.

**What is Semihosting?**
- Debug feature that lets bare-metal programs call host functions
- Print output, read files, exit with status codes
- Works with QEMU, OpenOCD, J-Link, Trace32

**Key Benefits:**
- Test bare-metal code without hardware
- Verify program output with `expect()` assertions
- Fast iteration cycle
- Works with existing SSpec framework

---

## Quick Start (3 Steps)

### 1. Install RISC-V Compiler

```bash
sudo apt install gcc-riscv64-unknown-elf
```

**Check installation:**
```bash
riscv64-unknown-elf-gcc --version
# Expected: gcc (GCC) 10.2.0 or later
```

### 2. Build Semihosting Binary

```bash
cd examples/baremetal
bash build_semihost.sh
```

**Expected output:**
```
╔════════════════════════════════════════════════════════════════╗
║  Building RISC-V 32 Semihosting Binary                        ║
╚════════════════════════════════════════════════════════════════╝

→ Assembling hello_riscv32_semihost.s...
→ Linking hello_riscv32_semihost.elf...

✓ Built: hello_riscv32_semihost.elf (896 bytes)

Testing with QEMU...
→ Running in QEMU...
Hello, RISC-V 32!
[SEMIHOST TEST] Success - exit code 0

✓ QEMU test complete

╔════════════════════════════════════════════════════════════════╗
║  Build Complete!                                               ║
╚════════════════════════════════════════════════════════════════╝
```

### 3. Run SSpec Tests

```bash
bin/simple test test/baremetal/hello_riscv32_semihost_spec.spl
```

**Expected output:**
```
RISC-V 32 Semihosting
  ✓ prints hello world message
  ✓ exits with code 0
  ✓ completes within timeout
  ✓ outputs success message

4 examples, 4 passed, 0 failed
```

---

## Architecture

```
SSpec Test
    ↓
SemihostExecutor.riscv32(binary, output_file)
    ↓
QemuInstance.start(config.with_semihosting())
    ↓
QEMU RISC-V 32 + semihosting enabled
    ↓
Binary calls: slli/ebreak/srai (semihosting)
    ↓
QEMU captures output → file
    ↓
SemihostExecutor.execute_and_capture()
    ↓
Read output file
    ↓
Return SemihostResult(stdout, exit_code, ...)
    ↓
expect(result.stdout).to_contain("Hello")
```

---

## File Structure

### Core Implementation (4 files, ~600 lines)

| File | Lines | Purpose |
|------|-------|---------|
| `src/lib/qemu/semihosting.spl` | ~150 | QEMU semihosting config |
| `src/lib/execution/semihost_capture.spl` | ~280 | Output capture executor |
| `examples/baremetal/hello_riscv32_semihost.s` | ~80 | Assembly example |
| `test/baremetal/hello_riscv32_semihost_spec.spl` | ~90 | SSpec tests |

### Support Files

- `examples/baremetal/build_semihost.sh` - Build script
- `doc/guide/semihosting_testing_quickstart.md` - This guide

---

## Usage Examples

### Example 1: Basic Test

```simple
use std.sspec.{describe, it, expect}
use lib.execution.semihost_capture.{SemihostExecutor}

describe "My Bare-Metal Test":
    it "prints output":
        val executor = SemihostExecutor.riscv32(
            "my_program.elf",
            "/tmp/output.txt"
        )?

        val result = executor.execute_and_capture()?

        expect(result.stdout).to_contain("Expected output")
        expect(result.exit_code).to_equal(0)

        executor.cleanup()
```

### Example 2: Multiple Tests

```simple
describe "Calculator Tests":
    var executor: SemihostExecutor? = nil

    after_each:
        if executor.?:
            executor.unwrap().cleanup()

    it "adds numbers":
        executor = SemihostExecutor.riscv32("calc.elf", "/tmp/out.txt")?
        val result = executor.unwrap().execute_and_capture()?
        expect(result.stdout).to_contain("2 + 2 = 4")

    it "multiplies numbers":
        executor = SemihostExecutor.riscv32("calc.elf", "/tmp/out.txt")?
        val result = executor.unwrap().execute_and_capture()?
        expect(result.stdout).to_contain("3 * 4 = 12")
```

### Example 3: x86_64 Support

```simple
it "works on x86_64":
    val executor = SemihostExecutor.x86_64(
        "examples/baremetal/hello_x86_64_semihost.elf",
        "/tmp/output.txt"
    )?

    val result = executor.execute_and_capture()?
    expect(result.stdout).to_contain("Hello, x86_64!")
```

---

## SemihostExecutor API

### Creation

```simple
# RISC-V 32-bit
SemihostExecutor.riscv32(binary: text, output_file: text) -> Result<SemihostExecutor, text>

# RISC-V 64-bit
SemihostExecutor.riscv64(binary: text, output_file: text) -> Result<SemihostExecutor, text>

# x86_64
SemihostExecutor.x86_64(binary: text, output_file: text) -> Result<SemihostExecutor, text>

# ARM
SemihostExecutor.arm(binary: text, output_file: text) -> Result<SemihostExecutor, text>
```

### Execution

```simple
me execute_and_capture() -> Result<SemihostResult, text>
```

**Returns:**
```simple
class SemihostResult:
    exit_code: i32      # Program exit code
    stdout: text        # Captured output
    stderr: text        # Error output (if any)
    duration_ms: i64    # Execution time
    success: bool       # exit_code == 0
```

### Cleanup

```simple
me cleanup()  # Stop QEMU, delete output file
```

---

## Writing Bare-Metal Programs

### RISC-V Semihosting Example

```asm
.section .text
.global _start

_start:
    # Print via semihosting SYS_WRITE0
    li a0, 0x04              # SYS_WRITE0
    la a1, message

    .option push
    .option norvc
    slli zero, zero, 0x1f    # Entry magic
    ebreak                    # Semihosting call
    srai zero, zero, 0x7     # Exit magic
    .option pop

    # Exit with code 0
    li a0, 0x18              # SYS_EXIT
    li a1, 0                 # Exit code

    .option push
    .option norvc
    slli zero, zero, 0x1f
    ebreak
    srai zero, zero, 0x7
    .option pop

halt:
    wfi
    j halt

.section .rodata
message:
    .asciz "Hello from bare-metal!\n"
```

### Build Commands

```bash
# Assemble
riscv64-unknown-elf-as -march=rv32i -mabi=ilp32 program.s -o program.o

# Link
riscv64-unknown-elf-ld -m elf32lriscv program.o -o program.elf -Ttext=0x80000000
```

---

## Troubleshooting

### Compiler Not Found

```
❌ Error: riscv64-unknown-elf-as not found
```

**Solution:**
```bash
sudo apt install gcc-riscv64-unknown-elf
```

### QEMU Not Found

```
⚠ qemu-system-riscv32 not found
```

**Solution:**
```bash
# Use project QEMU (already available)
ls resources/qemu/bin/qemu-system-riscv32

# Or install system QEMU
sudo apt install qemu-system-misc
```

### Binary Not Built

```
⊘ SKIP: Binary not built: examples/baremetal/hello_riscv32_semihost.elf
```

**Solution:**
```bash
cd examples/baremetal
bash build_semihost.sh
```

### No Output Captured

If `result.stdout` is empty:

1. Check QEMU output manually:
   ```bash
   qemu-system-riscv32 -M virt -kernel binary.elf \
       -nographic -semihosting-config enable=on,target=native
   ```

2. Check binary uses correct semihosting sequence
3. Verify `-semihosting-config` flag in QEMU args

### Test Timeout

If test hangs:

1. Binary might be in infinite loop
2. Check `wait_exit()` timeout (default: 10 seconds)
3. Verify binary exits properly (SYS_EXIT semihosting call)

---

## Next Steps

### Phase 2: Advanced Features (Optional)

1. **String Interning Protocol**
   - Add binary protocol parser
   - Integrate SemihostReader
   - 89% code size reduction

2. **Multiple Architectures**
   - Add ARM semihosting examples
   - Add x86_64 semihosting examples
   - Cross-architecture test suite

3. **Hardware Testing**
   - OpenOCD integration
   - J-Link support
   - Real hardware validation

---

## Reference

### Semihosting Operations

| Operation | Code | Description |
|-----------|------|-------------|
| SYS_OPEN | 0x01 | Open file |
| SYS_CLOSE | 0x02 | Close file |
| SYS_WRITEC | 0x03 | Write character |
| SYS_WRITE0 | 0x04 | Write null-terminated string |
| SYS_WRITE | 0x05 | Write bytes |
| SYS_READ | 0x06 | Read bytes |
| SYS_CLOCK | 0x10 | Get centiseconds |
| SYS_TIME | 0x11 | Get seconds |
| SYS_EXIT | 0x18 | Exit with status |

### QEMU Semihosting Flags

```bash
-semihosting-config enable=on,target=native  # Enable semihosting
-serial file:output.txt                       # Redirect to file
-serial stdio                                 # Redirect to stdout
-nographic                                    # No graphics
```

### Related Documentation

- **Design:** `doc/design/semihosting_system_api_design.md`
- **RISC-V Impl:** `src/baremetal/riscv/semihost.spl`
- **Reader:** `src/app/semihost/reader.spl`
- **Existing Tests:** `test/system/features/baremetal/semihosting_spec.spl`

---

**Status:** Phase 1 Complete ✅
**Ready for:** Production use with RISC-V 32 bare-metal testing
