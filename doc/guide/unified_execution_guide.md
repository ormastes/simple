# Unified Execution System - User Guide

**Version:** 0.5.0
**Date:** 2026-02-06
**Status:** Implementation Phase 1 Complete

## Overview

The Unified Execution System provides transparent local and remote execution for tests and debugging. The same test code runs unchanged on:

- **Local interpreter** - Direct Simple code execution
- **QEMU emulators** - RISC-V 32/64, ARM, x86_64 via GDB
- **Hardware debuggers** - Trace32, J-Link (future)

## Architecture

```
Test Code
    ↓
TestExecutor (Unified API)
    ↓
DebugAdapter (trait)
    ├─ LocalAdapter → InterpreterHookContext
    ├─ GdbMiAdapter → GDB MI → QEMU/Hardware
    └─ Trace32Adapter → Trace32 API (future)
```

## Quick Start

### Run Tests Locally

```simple
use lib.execution.mod.{ExecutionConfig, TestExecutor}

fn main():
    # Create local execution config
    val config = ExecutionConfig.local("my_test.spl")

    # Create executor
    val executor = TestExecutor.create(config)?

    # Run test
    val result = executor.execute()?

    # Cleanup
    executor.cleanup()

    if result.success:
        print("✓ Test passed: {result.output}")
    else:
        print("✗ Test failed: {result.error}")
```

### Run Tests on QEMU

```simple
use lib.execution.mod.{ExecutionConfig, TestExecutor}

fn main():
    # Create QEMU execution config (same API, different target!)
    val config = ExecutionConfig.qemu_riscv32("my_test.elf", gdb_port: 1234)

    # Create executor (automatically uses GDB adapter)
    val executor = TestExecutor.create(config)?

    # Run test (same code as local!)
    val result = executor.execute()?

    executor.cleanup()

    if result.success:
        print("✓ Test passed on QEMU")
    else:
        print("✗ Test failed on QEMU: {result.error}")
```

## Multi-Test Sessions

Run multiple tests with a single QEMU instance:

```simple
use lib.qemu.test_session.QemuMultiTestRunner
use lib.qemu.mod.QemuArch

fn main():
    # Create multi-test runner
    var runner = QemuMultiTestRunner.create(
        QemuArch.RiscV32,
        "baremetal_tests.elf"
    )

    # Add tests
    runner.add_test(\: test_boot())
    runner.add_test(\: test_memory_access())
    runner.add_test(\: test_interrupts())

    # Run all tests (single QEMU instance, auto-reset between tests)
    val results = runner.run_all()?

    # Print summary
    print("Tests: {runner.passed_count()}/{runner.tests.len()} passed")
```

## Session Lifecycle Management

Manual control over QEMU lifecycle:

```simple
use lib.qemu.test_session.QemuTestSession
use lib.qemu.mod.QemuArch

fn main():
    # Create session
    val session = QemuTestSession.create(QemuArch.RiscV32, "test.elf")
        .with_gdb_port(1234)
        .with_auto_reset(true)

    # Start QEMU + GDB
    session.start()?

    # Run test 1
    session.run_test(\: test_basic())?
    # Automatic reset here

    # Run test 2
    session.run_test(\: test_advanced())?
    # Automatic reset here

    # Manual reset
    session.reset()?

    # Reload binary (for testing updated code)
    session.reload()?

    # Stop QEMU
    session.stop()
```

## Test Runner Integration

Use with command-line flag:

```bash
# Run locally (default)
bin/simple test test/my_spec.spl

# Run on QEMU RISC-V 32
bin/simple test test/my_spec.spl --target=riscv32-qemu

# Run on QEMU x86_64
bin/simple test test/my_spec.spl --target=x86_64-qemu

# Run on custom target
bin/simple test test/my_spec.spl --target=riscv32-qemu:localhost:5555
```

## Configuration Options

### ExecutionConfig Options

| Option | Description | Local | QEMU | Trace32 |
|--------|-------------|-------|------|---------|
| `target` | Target identifier | `"local"` | `"riscv32-qemu"` | `"arm32-trace32"` |
| `program` | Program path | `.spl` file | `.elf` file | `.elf` file |
| `clear_context` | Clear state between tests | ✅ | ❌ | ❌ |
| `reload_program` | Reload binary | ❌ | ✅ | ✅ |
| `execution_timeout_ms` | Max execution time | 30s | 60s | 60s |

### Target Strings

| Target | Format | Example |
|--------|--------|---------|
| Local | `local` | `ExecutionConfig.local("test.spl")` |
| QEMU RISC-V 32 | `riscv32-qemu` | `ExecutionConfig.qemu_riscv32("test.elf", 1234)` |
| QEMU x86_64 | `x86_64-qemu` | `ExecutionConfig.qemu_x86_64("test.elf", 1234)` |
| Custom | `arch-backend:host:port` | `parse_target("riscv32-qemu:localhost:5555", "test.elf")` |

## Adapter Capabilities

Each adapter reports what features it supports:

```simple
use app.dap.adapter.local.LocalAdapter
use app.dap.adapter.gdb_mi.GdbMiAdapter

# Local adapter capabilities
val local = LocalAdapter.create(config)
val caps = local.get_capabilities()
assert(caps.can_clear_context == true)  # ✅
assert(caps.supports_memory == false)   # ❌

# GDB adapter capabilities
val gdb = GdbMiAdapter.connect(config)?
val caps = gdb.get_capabilities()
assert(caps.supports_memory == true)    # ✅
assert(caps.supports_registers == true) # ✅
assert(caps.can_clear_context == false) # ❌
```

## Context Isolation

The system provides automatic context isolation between tests:

### Local Execution
- Clears interpreter state
- Resets global variables
- Cleans breakpoints

### Remote Execution (QEMU)
- Reloads ELF binary
- Resets target CPU
- Re-initializes memory

## Example: Bare-Metal Test Suite

```simple
use lib.qemu.test_session.QemuMultiTestRunner
use lib.qemu.mod.QemuArch

fn main():
    var runner = QemuMultiTestRunner.create(
        QemuArch.RiscV32,
        "examples/baremetal/timer_riscv32.elf"
    )

    # Boot test
    runner.add_test(\:
        # QEMU starts in machine mode
        # Test verifies CSR access works
        check_machine_mode()?
        Ok("boot test passed")
    )

    # Timer test
    runner.add_test(\:
        # Reset between tests (automatic)
        # Test timer interrupt
        test_timer_interrupt()?
        Ok("timer test passed")
    )

    # Memory test
    runner.add_test(\:
        # Fresh state (automatic reload)
        # Test memory read/write
        test_memory_rw()?
        Ok("memory test passed")
    )

    # Run all with single QEMU instance
    val results = runner.run_all()?

    # Print results
    for (i, result) in results.enumerate():
        if result.success:
            print("✓ Test {i + 1}: {result.output}")
        else:
            print("✗ Test {i + 1}: {result.error}")

    print("\nSummary: {runner.passed_count()}/{runner.tests.len()} passed")
```

## Error Handling

All operations return `Result<T, text>`:

```simple
val executor_result = TestExecutor.create(config)
match executor_result:
    Ok(executor):
        val result = executor.execute()?
        executor.cleanup()
    Err(e):
        print("Failed to create executor: {e}")
        # Fallback or skip test
```

## Performance

- **Local execution**: Native speed
- **QEMU execution**: 2-10x slower (acceptable for testing)
- **Session reuse**: 10x faster than restarting QEMU per test

## Troubleshooting

### QEMU fails to start
```
Error: qemu-system-riscv32 not found
```
**Solution**: Install QEMU or use project binaries:
```bash
sudo apt install qemu-system-arm qemu-system-misc
# Or use project binaries in resources/qemu/bin/
```

### GDB connection fails
```
Error: failed to connect to GDB
```
**Solution**: Check QEMU GDB stub is listening:
```bash
ss -tlnp | grep :1234
```

### Test timeout
```
Error: QEMU did not exit within 30000ms
```
**Solution**: Increase timeout in config:
```simple
val config = ExecutionConfig.qemu_riscv32("test.elf", 1234)
config.execution_timeout_ms = 120000  # 2 minutes
```

## Future Enhancements

- [ ] Trace32 adapter (hardware debugging)
- [ ] J-Link adapter
- [ ] Serial output capture
- [ ] Memory inspection API
- [ ] Multi-threaded debugging
- [ ] Watchpoint support

## See Also

- `doc/architecture/dap_adapter_architecture.md` - Adapter layer design
- `doc/guide/qemu_integration_guide.md` - QEMU setup
- `test/lib/unified_execution_spec.spl` - Test suite
- `examples/baremetal/` - Bare-metal examples
