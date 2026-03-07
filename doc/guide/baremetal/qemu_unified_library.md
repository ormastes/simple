# QEMU Unified Library Guide

**Location:** `src/lib/qemu/mod.spl`

The QEMU unified library provides a shared implementation for managing QEMU instances across different use cases:
- **Remote debugging** (GDB stub integration)
- **Bare-metal testing** (test harness)
- **Embedded test runner** (stdio/serial transport)

## Overview

Previously, QEMU logic was duplicated across:
- `src/remote/test/qemu_runner.spl` - Remote debugging (163 lines)
- `src/app/test_runner/host/loader.spl` - Test runner (278 lines)

Now consolidated into a single unified library with:
- **Multi-architecture support** (x86, x86_64, ARM32, ARM64, RISC-V 32/64)
- **Flexible configuration** (GDB, serial, debug-exit)
- **Process management** (start/stop/wait/is_running)
- **Exit code interpretation** (debug-exit device encoding)

---

## Quick Start

### Remote Debugging

```simple
use lib.qemu.{QemuArch, QemuConfig, QemuInstance}

# Create config for remote debugging
val config = QemuConfig.for_remote_debug(
    QemuArch.RiscV32,
    "firmware.elf",
    1234  # GDB port
)

# Start QEMU with GDB stub
val result = QemuInstance.start(config)
match result:
    case Ok(instance):
        print "Connect with: gdb-multiarch -ex 'target remote :1234'"

        # QEMU is halted, waiting for debugger
        # ... debug session ...

        var inst = instance
        inst.stop()

    case Err(msg):
        print "Error: {msg}"
```

### Bare-Metal Testing

```simple
use lib.qemu.{QemuArch, QemuConfig, QemuInstance, interpret_exit_code}

# Create config for test runner
val config = QemuConfig.for_test_runner(
    QemuArch.X86,
    "test.elf"
)

# Start QEMU
val result = QemuInstance.start(config)
match result:
    case Ok(instance):
        # Wait for test to complete
        val exit_result = instance.wait_exit(10000)  # 10s timeout

        match exit_result:
            case Ok(exit_code):
                val interpretation = interpret_exit_code(exit_code, true)
                if interpretation.success:
                    print "✓ Tests passed"
                else:
                    print "✗ Tests failed: {interpretation.message}"

            case Err(msg):
                print "✗ Timeout: {msg}"

    case Err(msg):
        print "Error: {msg}"
```

---

## Architecture

### Type Hierarchy

```
QemuArch (enum)
├── X86
├── X86_64
├── ARM32
├── ARM64
├── RiscV32
└── RiscV64

QemuConfig (class)
├── arch: QemuArch
├── binary_path: text
├── machine: text
├── memory: text
├── GDB config (enabled, port, wait)
├── Serial config (stdio, file)
├── Exit config (debug_exit, no_reboot)
├── Display config (no_graphic, no_display)
└── extra_args: [text]

QemuInstance (class)
├── config: QemuConfig
├── pid: text
└── running: bool
```

### Methods

#### QemuArch

| Method | Description | Example |
|--------|-------------|---------|
| `qemu_command()` | Get QEMU binary name | `"qemu-system-riscv32"` |
| `default_machine()` | Get default machine type | `"virt"` |
| `default_memory()` | Get default RAM size | `"128M"` |
| `from_string(s)` | Parse from string | `QemuArch.from_string("x86")` |

#### QemuConfig

| Method | Description | Example |
|--------|-------------|---------|
| `for_remote_debug(arch, elf, port)` | Create debug config | GDB stub enabled, halted start |
| `for_test_runner(arch, elf)` | Create test config | Serial stdio, debug-exit enabled |
| `build_args()` | Build command-line args | `["-machine", "virt", ...]` |

#### QemuInstance

| Method | Description | Example |
|--------|-------------|---------|
| `start(config)` | Start QEMU | Returns `Result<QemuInstance, text>` |
| `stop()` | Stop QEMU | Kills process (SIGTERM then SIGKILL) |
| `is_running()` | Check if running | Returns `bool` |
| `wait_exit(timeout_ms)` | Wait for exit | Returns `Result<i32, text>` |
| `get_pid()` | Get process ID | Returns `text` |
| `get_gdb_port()` | Get GDB port | Returns `i32` |

---

## Configuration Examples

### Minimal Remote Debug Config

```simple
val config = QemuConfig.for_remote_debug(
    QemuArch.RiscV32,
    "firmware.elf",
    1234
)

# Defaults:
# - machine: "virt"
# - memory: "128M"
# - gdb_enabled: true
# - gdb_port: 1234
# - gdb_wait: true (start halted)
# - no_graphic: true
```

### Minimal Test Runner Config

```simple
val config = QemuConfig.for_test_runner(
    QemuArch.X86,
    "test.elf"
)

# Defaults:
# - machine: "pc"
# - memory: "128M"
# - serial_stdio: true
# - debug_exit: true (isa-debug-exit device on x86)
# - no_reboot: true
# - no_display: true
```

### Custom Config

```simple
var config = QemuConfig.for_test_runner(
    QemuArch.ARM32,
    "firmware.elf"
)

# Customize settings
config.machine = "lm3s6965evb"  # Stellaris (Cortex-M3)
config.memory = "16M"
config.serial_file = "uart.log"  # Log serial to file
config.extra_args = [
    "-semihosting-config", "enable=on,target=native",
    "-monitor", "none"
]
```

---

## Multi-Architecture Support

### Supported Architectures

| Architecture | QEMU Command | Default Machine | Default RAM |
|--------------|--------------|-----------------|-------------|
| X86 | `qemu-system-i386` | `pc` | 128M |
| X86_64 | `qemu-system-x86_64` | `pc` | 128M |
| ARM32 | `qemu-system-arm` | `lm3s6965evb` | 16M |
| ARM64 | `qemu-system-aarch64` | `virt` | 128M |
| RiscV32 | `qemu-system-riscv32` | `virt` | 128M |
| RiscV64 | `qemu-system-riscv64` | `virt` | 128M |

### Architecture Detection

```simple
use lib.qemu.{QemuArch, is_qemu_available}

# Check if QEMU is installed
if is_qemu_available(QemuArch.RiscV32):
    print "QEMU RISC-V 32 is available"
else:
    print "Install with: apt install qemu-system-misc"

# Parse from string (flexible)
val arch = QemuArch.from_string("arm")      # → QemuArch.ARM32
val arch = QemuArch.from_string("cortex-m") # → QemuArch.ARM32
val arch = QemuArch.from_string("rv32")     # → QemuArch.RiscV32
```

---

## Exit Code Interpretation

### Debug Exit Device (x86)

The `isa-debug-exit` device on x86 encodes exit codes:
```
actual_code = (exit_code << 1) | 1
```

So:
- `exit(0)` → QEMU exits with `1`
- `exit(1)` → QEMU exits with `3`

Use `interpret_exit_code()` to decode:

```simple
use lib.qemu.{interpret_exit_code}

val result = interpret_exit_code(1, true)  # true = has debug-exit device
# → ExitCodeResult(success: true, message: "Tests passed (exit 0)")

val result = interpret_exit_code(3, true)
# → ExitCodeResult(success: false, message: "Tests failed (exit 1)")
```

### Normal Exit Codes

```simple
val result = interpret_exit_code(0, false)  # false = no debug-exit
# → ExitCodeResult(success: true, message: "Tests passed")

val result = interpret_exit_code(124, false)
# → ExitCodeResult(success: false, message: "Timeout")

val result = interpret_exit_code(137, false)
# → ExitCodeResult(success: false, message: "Killed (SIGKILL)")
```

---

## Toolchain Detection

### Check QEMU Installation

```simple
use lib.qemu.{is_qemu_available, QemuArch}

if not is_qemu_available(QemuArch.X86):
    print "Please install QEMU: sudo apt install qemu-system-x86"
```

### Find GDB for Architecture

```simple
use lib.qemu.{find_gdb, is_gdb_available, QemuArch}

val gdb = find_gdb(QemuArch.RiscV32)
if gdb.len() > 0:
    print "Found GDB: {gdb}"
else:
    print "Install GDB: sudo apt install gdb-multiarch"

# Or check availability
if is_gdb_available(QemuArch.RiscV32):
    print "GDB is available for RISC-V"
```

### Find Cross-Compiler

```simple
use lib.qemu.{find_rv32_gcc, is_rv32_gcc_available}

val gcc = find_rv32_gcc()
if gcc.len() > 0:
    print "Found RISC-V GCC: {gcc}"

# Or check availability
if is_rv32_gcc_available():
    print "RISC-V cross-compiler is available"
else:
    print "Install: sudo apt install gcc-riscv64-unknown-elf"
```

---

## Advanced Usage

### Build RISC-V Binary

```simple
use lib.qemu.{build_rv32_binary}

val result = build_rv32_binary(
    "test.S",       # Assembly source
    "test.elf"      # Output binary
)

match result:
    case Ok(path):
        print "Built: {path}"
    case Err(msg):
        print "Build failed: {msg}"
```

### Process Management

```simple
use lib.qemu.{QemuConfig, QemuInstance, QemuArch}

val config = QemuConfig.for_test_runner(QemuArch.X86, "test.elf")
val result = QemuInstance.start(config)

match result:
    case Ok(instance):
        # Check if still running
        while instance.is_running():
            print "QEMU is running (PID: {instance.get_pid()})"
            shell("sleep 1")

        # Wait with timeout
        val exit_result = instance.wait_exit(30000)  # 30s

        # Or stop manually
        var inst = instance
        inst.stop()
```

---

## Migration Guide

### From Remote QEMU Runner

**Before:**
```simple
use remote.test.qemu_runner.{QemuRunner}

val runner = QemuRunner.start("test.elf", 1234)?
# ...
runner.stop()
```

**After:**
```simple
use lib.qemu.{QemuArch, QemuConfig, QemuInstance}

val config = QemuConfig.for_remote_debug(QemuArch.RiscV32, "test.elf", 1234)
val instance = QemuInstance.start(config)?
# ...
var inst = instance
inst.stop()
```

### From Test Runner Loader

**Before:**
```simple
use app.test_runner.host.loader.{LoaderConfig, Loader}

val config = LoaderConfig_qemu("test.elf", "x86")
var loader = Loader_create(config)
loader.start()
# ...
loader.stop()
```

**After:**
```simple
use lib.qemu.{QemuArch, QemuConfig, QemuInstance}

val config = QemuConfig.for_test_runner(QemuArch.X86, "test.elf")
val instance = QemuInstance.start(config)?
# ...
var inst = instance
inst.stop()
```

---

## Backward Compatibility

Both `src/remote/test/qemu_runner.spl` and `src/app/test_runner/host/loader.spl` have been updated to use the unified library internally, maintaining their original APIs:

```simple
# Remote debugging wrapper (backward compatible)
use remote.test.qemu_runner.{QemuRunner}

val runner = QemuRunner.start("test.elf", 1234)?  # Still works!

# Test runner loader (backward compatible)
use app.test_runner.host.loader.{Loader, LoaderConfig}

val config = LoaderConfig_qemu("test.elf", "x86")
var loader = Loader_create(config)  # Still works!
```

---

## See Also

- **Example:** `examples/qemu/unified_runner_example.spl`
- **Tests:** `test/lib/qemu_spec.spl`
- **Remote Debugging:** `doc/guide/remote_debugging.md`
- **Test Runner:** `doc/guide/embedded_test_runner.md`
