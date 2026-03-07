# Bare-Metal Programming

**Version:** 0.5.0
**Status:** Production (QEMU), Development (Hardware Debugging)

---

## Overview

Simple supports bare-metal programming for embedded targets. Write programs in Simple or assembly, test in QEMU, and deploy to real hardware via OpenOCD, J-Link, or Trace32.

**Supported Targets:**

| Architecture | QEMU | Hardware | Status |
|-------------|------|----------|--------|
| ARM Cortex-M | Yes | STM32F4 | Production |
| x86_64 | Yes | -- | Production |
| RISC-V 32 | Yes | -- | Production |
| RISC-V 64 | Yes | -- | Development |

---

## Quick Start

### 1. Choose a Target

```bash
# ARM Cortex-M (most common embedded target)
bin/simple build --target=arm-cortex-m4 examples/baremetal/hello_arm.spl

# x86_64 bare-metal
bin/simple build --target=x86_64-baremetal examples/baremetal/hello_x86.spl

# RISC-V 32-bit
bin/simple build --target=riscv32-baremetal examples/baremetal/hello_riscv32.spl
```

### 2. Test in QEMU

```bash
# ARM
qemu-system-arm -M lm3s6965evb -kernel hello_arm.elf -nographic -semihosting

# x86_64
qemu-system-x86_64 -kernel hello_x86.elf -nographic -no-reboot

# RISC-V 32
qemu-system-riscv32 -M virt -kernel hello_riscv32.elf -nographic -semihosting
```

### 3. Run SSpec Tests

```bash
bin/simple test test/baremetal/hello_riscv32_semihost_spec.spl
```

---

## QEMU Setup

### Installation

```bash
# Ubuntu/Debian
sudo apt install qemu-system-arm qemu-system-misc qemu-system-x86

# macOS
brew install qemu

# From source (for latest features)
git clone https://github.com/qemu/qemu.git
cd qemu
./configure --target-list=arm-softmmu,riscv32-softmmu,riscv64-softmmu,x86_64-softmmu
make -j$(nproc)
```

### Verify Installation

```bash
qemu-system-arm --version
qemu-system-riscv32 --version
qemu-system-x86_64 --version
```

### Required Features

| Feature | Flag | Purpose |
|---------|------|---------|
| Semihosting | `--enable-semihosting` | Host I/O from bare-metal |
| TCG | default | Software CPU emulation |
| GDB stub | `--enable-debug-tcg` | GDB debugging |

---

## QEMU Unified Library

Simple provides a unified QEMU library for programmatic control:

### API

```simple
use std.qemu.{QemuArch, QemuConfig, QemuInstance}

# Configure QEMU instance
val config = QemuConfig(
    arch: QemuArch.RiscV32,
    machine: "virt",
    binary: "my_program.elf",
    memory: "128M",
    semihosting: true,
    gdb_port: nil
)

# Start and run
val instance = QemuInstance.start(config)?
val exit_code = instance.wait_exit(timeout_ms: 10000)?
instance.stop()
```

### Supported Architectures

```simple
enum QemuArch:
    Arm           # ARM Cortex-A/R/M
    AArch64       # ARM 64-bit
    RiscV32       # RISC-V 32-bit
    RiscV64       # RISC-V 64-bit
    X86_64        # x86-64
```

### Machine Types

| Architecture | Machine | Description |
|-------------|---------|-------------|
| ARM | `lm3s6965evb` | Stellaris LM3S6965 (Cortex-M3) |
| ARM | `mps2-an385` | ARM MPS2 AN385 (Cortex-M3) |
| ARM | `virt` | Generic ARM virtual platform |
| RISC-V 32 | `virt` | Generic RISC-V virtual platform |
| x86_64 | `q35` | Intel Q35 chipset |

### Exit Code Interpretation

QEMU exit codes encode the program's actual exit status:

```simple
fn interpret_exit(qemu_code: i32, arch: QemuArch) -> i32:
    match arch:
        QemuArch.RiscV32:
            (qemu_code >> 1) - 1   # RISC-V semihosting encoding
        QemuArch.Arm:
            qemu_code & 0xFF       # ARM semihosting encoding
        _:
            qemu_code
```

### Toolchain Detection

```simple
use std.qemu.{detect_toolchain}

val toolchain = detect_toolchain(QemuArch.RiscV32)?
print "Assembler: {toolchain.assembler}"
print "Linker: {toolchain.linker}"
print "GDB: {toolchain.gdb}"
```

---

## Semihosting

Semihosting lets bare-metal programs call host functions (print, file I/O, exit) via debug channels.

### How It Works

```
Bare-metal program
    |
    v
Semihosting call (special instruction sequence)
    |
    v
QEMU/debugger intercepts
    |
    v
Host executes operation (print, file read, exit)
    |
    v
Result returned to program
```

### RISC-V Semihosting Sequence

```asm
# Magic instruction sequence recognized by QEMU
.option push
.option norvc
slli zero, zero, 0x1f    # Entry marker
ebreak                    # Trigger semihosting
srai zero, zero, 0x7     # Exit marker
.option pop
```

### Semihosting Operations

| Operation | Code | Description |
|-----------|------|-------------|
| `SYS_OPEN` | `0x01` | Open file |
| `SYS_CLOSE` | `0x02` | Close file |
| `SYS_WRITEC` | `0x03` | Write single character |
| `SYS_WRITE0` | `0x04` | Write null-terminated string |
| `SYS_WRITE` | `0x05` | Write bytes to file |
| `SYS_READ` | `0x06` | Read bytes from file |
| `SYS_CLOCK` | `0x10` | Get time in centiseconds |
| `SYS_TIME` | `0x11` | Get time in seconds |
| `SYS_EXIT` | `0x18` | Exit with status code |

### RISC-V Assembly Example

```asm
.section .text
.global _start

_start:
    # Print "Hello" via SYS_WRITE0
    li a0, 0x04
    la a1, message

    .option push
    .option norvc
    slli zero, zero, 0x1f
    ebreak
    srai zero, zero, 0x7
    .option pop

    # Exit with code 0 via SYS_EXIT
    li a0, 0x18
    li a1, 0

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

### Build and Run

```bash
# Assemble
riscv64-unknown-elf-as -march=rv32i -mabi=ilp32 hello.s -o hello.o

# Link
riscv64-unknown-elf-ld -m elf32lriscv hello.o -o hello.elf -Ttext=0x80000000

# Run in QEMU
qemu-system-riscv32 -M virt -kernel hello.elf \
    -nographic -semihosting-config enable=on,target=native
```

---

## SSpec Testing with Semihosting

### SemihostExecutor API

```simple
use std.execution.semihost_capture.{SemihostExecutor, SemihostResult}

# Create executor for target architecture
SemihostExecutor.riscv32(binary: text, output_file: text) -> Result<SemihostExecutor, text>
SemihostExecutor.riscv64(binary: text, output_file: text) -> Result<SemihostExecutor, text>
SemihostExecutor.arm(binary: text, output_file: text) -> Result<SemihostExecutor, text>
SemihostExecutor.x86_64(binary: text, output_file: text) -> Result<SemihostExecutor, text>
```

### SemihostResult

```simple
class SemihostResult:
    exit_code: i32      # Program exit code
    stdout: text        # Captured output
    stderr: text        # Error output (if any)
    duration_ms: i64    # Execution time
    success: bool       # exit_code == 0
```

### Test Example

```simple
use std.sspec.{describe, it, expect}
use std.execution.semihost_capture.{SemihostExecutor}

describe "RISC-V 32 Semihosting":
    it "prints hello world message":
        val executor = SemihostExecutor.riscv32(
            "examples/baremetal/hello_riscv32_semihost.elf",
            "/tmp/output.txt"
        )?

        val result = executor.execute_and_capture()?

        expect(result.stdout).to_contain("Hello")
        expect(result.exit_code).to_equal(0)

        executor.cleanup()
```

### Multiple Tests with Cleanup

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

---

## Embedded Hardware Debugging

### Supported Configurations

| Target | Debug Probe | Connection | Status |
|--------|------------|------------|--------|
| STM32F4 | ST-LINK V2 | OpenOCD | Production |
| STM32F4 | Trace32 | Lauterbach | Production |
| STM32F4 | J-Link | OpenOCD | Development |
| ARM Cortex-M | QEMU | GDB stub | Production |
| RISC-V | QEMU | GDB stub | Production |
| RISC-V | OpenOCD | JTAG | Development |

### OpenOCD Setup

```bash
# Install
sudo apt install openocd

# Connect to STM32F4 via ST-LINK
openocd -f interface/stlink.cfg -f target/stm32f4x.cfg

# Flash and debug
openocd -f interface/stlink.cfg -f target/stm32f4x.cfg \
    -c "program my_program.elf verify reset exit"
```

### GDB Debugging

```bash
# Start QEMU with GDB stub
qemu-system-riscv32 -M virt -kernel program.elf -nographic -s -S

# Connect GDB (in another terminal)
riscv64-unknown-elf-gdb program.elf
(gdb) target remote :1234
(gdb) break main
(gdb) continue
```

### Trace32 (Lauterbach)

For professional embedded debugging with the Lauterbach Trace32 system:

```bash
# Configure connection
# Hardware: Lauterbach PowerTrace -> JTAG -> STM32F4 board

# Load PRACTICE script
t32 -s startup.cmm
```

Key Trace32 features:
- Real-time trace capture
- Flash programming
- RTOS-aware debugging
- Code coverage analysis

### Hardware Inventory

| Item | Model | Connection |
|------|-------|------------|
| Target board | STM32F4-Discovery | USB + JTAG |
| Debug probe (basic) | ST-LINK V2 | USB |
| Debug probe (advanced) | Lauterbach PowerTrace | USB + JTAG |
| Debug probe (alt) | SEGGER J-Link | USB + SWD/JTAG |

---

## Platform-Specific Details

### ARM Cortex-M

**Memory Map:**
```
0x00000000 - 0x000FFFFF  Flash (1MB)
0x20000000 - 0x2001FFFF  SRAM (128KB)
0x40000000 - 0x5FFFFFFF  Peripherals
0xE0000000 - 0xE00FFFFF  System (NVIC, SysTick, etc.)
```

**Startup Code:**
```simple
# ARM Cortex-M startup
@section(".vectors")
val vector_table = [
    stack_top,      # Initial SP
    reset_handler,  # Reset vector
    nmi_handler,    # NMI
    hardfault_handler,  # HardFault
]

@entry
fn reset_handler():
    # Initialize .data and .bss
    # Call main
    main()
```

**Linker Script:**
```ld
MEMORY {
    FLASH (rx) : ORIGIN = 0x00000000, LENGTH = 1M
    SRAM (rwx) : ORIGIN = 0x20000000, LENGTH = 128K
}

SECTIONS {
    .text : { *(.vectors) *(.text*) } > FLASH
    .rodata : { *(.rodata*) } > FLASH
    .data : { *(.data*) } > SRAM AT > FLASH
    .bss : { *(.bss*) } > SRAM
}
```

### x86_64 Bare-Metal

**Memory Layout:**
```
0x00000000 - 0x000FFFFF  Real mode / legacy
0x00100000 - ...         Kernel load address (1MB+)
```

**Multiboot Header:**
```simple
@section(".multiboot")
val multiboot_header = [
    0x1BADB002,  # Magic
    0x00000003,  # Flags (align + meminfo)
    0xE4524FFB,  # Checksum
]
```

### RISC-V

**Memory Layout (QEMU virt):**
```
0x80000000 - ...  RAM start (default)
```

**Build Commands:**
```bash
# RV32I
riscv64-unknown-elf-as -march=rv32i -mabi=ilp32 prog.s -o prog.o
riscv64-unknown-elf-ld -m elf32lriscv prog.o -o prog.elf -Ttext=0x80000000

# RV64I
riscv64-unknown-elf-as -march=rv64i -mabi=lp64 prog.s -o prog.o
riscv64-unknown-elf-ld prog.o -o prog.elf -Ttext=0x80000000
```

---

## QEMU Flags Reference

| Flag | Description |
|------|-------------|
| `-M <machine>` | Machine type (virt, lm3s6965evb, etc.) |
| `-kernel <file>` | Kernel/program ELF file |
| `-nographic` | No graphical display |
| `-semihosting` | Enable semihosting (basic) |
| `-semihosting-config enable=on,target=native` | Enable with native target |
| `-serial file:output.txt` | Redirect serial to file |
| `-serial stdio` | Redirect serial to stdout |
| `-s` | Start GDB server on port 1234 |
| `-S` | Pause at startup (wait for GDB) |
| `-m <size>` | Memory size (e.g., `128M`) |
| `-d <items>` | Debug output (e.g., `in_asm,cpu`) |

---

## Troubleshooting

| Issue | Cause | Fix |
|-------|-------|-----|
| `riscv64-unknown-elf-as not found` | Compiler not installed | `sudo apt install gcc-riscv64-unknown-elf` |
| `qemu-system-riscv32 not found` | QEMU not installed | `sudo apt install qemu-system-misc` |
| Binary not built error | Missing build step | Run `bash build_semihost.sh` in `examples/baremetal/` |
| No output captured | Wrong semihosting config | Check `-semihosting-config` flag |
| Test timeout/hang | Binary infinite loop | Verify binary uses SYS_EXIT semihosting call |
| OpenOCD connection refused | Wrong interface config | Match config to your debug probe model |
| Flash programming fails | Target locked | Use mass erase before programming |
| GDB can't find symbols | Binary stripped | Build with debug info (`-g` flag) |

---

## Related Documentation

- Backend overview: `doc/guide/backend/backends.md`
- GPU programming: `doc/guide/backend/gpu_programming.md`
- SSpec framework: See `/sspec` skill
