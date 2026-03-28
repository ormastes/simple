# simple_test - BDD Test Runner

## Overview

Runs BDD-style spec tests with formatted output, timing, and summary.

In the current repo, the user-facing entrypoint is normally:

```bash
bin/simple test ...
```

This document also covers the remote baremetal lanes exercised through that
command.

## Current Baremetal Status

Observed on this host on 2026-03-23:

- `test/feature/baremetal/ghdl_riscv32_semihost_spec.spl` passes end to end with `ghdl`
- `test/integration/debug/hardware/stm32wb_openocd_spec.spl` passes as a repo-readiness spec
- `test/integration/debug/hardware/stm32h7_openocd_spec.spl` passes as a repo-readiness spec
- `test/integration/debug/hardware/stm32wb_stlink_spec.spl` passes as a checked-config spec
- `test/integration/debug/hardware/stm32h7_stlink_spec.spl` passes as a checked-config spec
- `test/integration/debug/hardware/hardware_check_spec.spl` passes and confirms local tool presence
- `test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl` still has failures and stale assumptions
- composite remote `--mode=interpreter(remote(baremetal(...)))` is currently not preserved by the Rust CLI entrypoint and falls back to plain interpreter mode

In practice this means:

- the STM lanes are currently useful for readiness/config validation and for the live helper smokes inside the remote-baremetal feature spec
- the RTL RISC-V32 emulator lane is the only checked-in baremetal lane that currently runs fully end to end in normal local use
- TRACE32 remains blocked by a mix of host startup issues and one repo-side spec/runtime issue

## Usage

```bash
simple_test                        # Run all tests in test/
simple_test test/unit/             # Run tests in directory
simple_test test/main_spec.spl     # Run single test file
simple_test --filter "json"        # Run tests matching pattern
simple_test --watch                # Watch mode (rerun on changes)
simple_test --verbose              # Show all test output
simple_test --json                 # JSON output for CI
```

## Options

| Flag | Description |
|------|-------------|
| `--filter <pattern>` | Run only tests matching pattern |
| `--watch` | Watch mode, rerun on file changes |
| `--verbose` | Show all output including passing |
| `--json` | JSON output format |
| `--parallel` | Run tests in parallel |
| `--timeout <ms>` | Test timeout (default: 5000) |
| `--fail-fast` | Stop on first failure |

## Remote Baremetal Usage

For remote-interpreter and hardware-backed lanes, use environment selection
instead of treating `--target` as the runtime selector.

Recommended forms:

```bash
# QEMU RV32 compatibility path
# Note: the Rust CLI currently warns that this mode is unknown and falls back
# to interpreter mode. Keep this command documented because it is still the
# intended mode shape, but do not treat it as a verified CLI path yet.
bin/simple test test/integration/baremetal/qemu_baremetal_lib_smoke_spec.spl \
  '--mode=interpreter(remote(baremetal(riscv32)))'

# RTL RV32I emulator path that works on this host today
bin/simple test test/feature/baremetal/ghdl_riscv32_semihost_spec.spl

# OpenOCD STM readiness lanes
bin/simple test test/integration/debug/hardware/stm32wb_openocd_spec.spl
bin/simple test test/integration/debug/hardware/stm32h7_openocd_spec.spl

# ST-Link metadata/config lanes
bin/simple test test/integration/debug/hardware/stm32wb_stlink_spec.spl
bin/simple test test/integration/debug/hardware/stm32h7_stlink_spec.spl

# TRACE32 STM readiness lanes
bin/simple test test/integration/debug/hardware/t32_native_spec.spl
bin/simple test test/integration/debug/hardware/t32_gdb_bridge_spec.spl
```

### Current Meaning Of The STM Specs

Today the STM-related specs split into two classes:

- repo-readiness/config specs:
  - `stm32wb_openocd_spec.spl`
  - `stm32h7_openocd_spec.spl`
  - `stm32wb_stlink_spec.spl`
  - `stm32h7_stlink_spec.spl`
- host-aware live smoke helpers:
  - `test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl`

The first class verifies checked-in board metadata, helper fixture presence,
and launch command construction. They do not by themselves prove full on-device
test execution.

The second class attempts live debugger/transport checks and is closer to a
system smoke, but it is currently not cleanly green because:

- the TRACE32 branch still fails before it can classify the host state cleanly
- one expectation in that spec drifted after an ELF fixture was added

### Current Meaning Of The RTL RISC-V32 Emulator Spec

`test/feature/baremetal/ghdl_riscv32_semihost_spec.spl` is currently the most
representative working baremetal lane in-tree. It exercises:

- checked-in RV32 ELF fixtures
- ELF-to-VHDL memory package conversion through `ghdl_runner.shs`
- GHDL simulation of the repo's RV32I RTL
- semihosted output collection
- pass/fail parsing through the normal test command

This is a real execution lane, not just a wiring/readiness check.

### Current Meaning Of The TRACE32 Specs

Today the TRACE32 specs are readiness specs, not full hardware verification.
They validate:

- repo-managed helper files
- expected launcher paths
- expected Remote API and GDB port commands
- shared STM smoke fixture presence

They do not yet prove real on-device execution because that still depends on a
working local TRACE32 PowerView session.

On this host on 2026-03-23, direct `t32rem ... PING` still times out, so these
lanes should still be treated as blocked for full execution.

### TRACE32 Bring-Up Helpers

The repo-managed bring-up sequence is:

```bash
./scripts/t32_start_stm.shs stm32wb native
./scripts/t32_check_ready.shs
./scripts/t32_enable_gdb.shs localhost 20000 2331
```

See `doc/07_guide/backend/trace32_linux_setup.md` for the host-side setup.

## Output Format

### Default (Pretty)

```
simple_test v0.1.0

Running tests...

  core/json_spec.spl
    ✓ parse should handle empty object (2ms)
    ✓ parse should handle nested objects (5ms)
    ✗ parse should handle unicode (3ms)
      Expected: "こんにちは"
      Received: "???????"
    ✓ stringify should format numbers (1ms)

  core/string_spec.spl
    ✓ split should work with delimiter (1ms)
    ✓ trim should remove whitespace (0ms)
    ✓ replace should handle multiple (2ms)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Tests:  6 passed, 1 failed, 7 total
Time:   14ms
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### JSON

```json
{
  "suites": [
    {
      "file": "core/json_spec.spl",
      "tests": [
        {
          "name": "parse should handle empty object",
          "status": "passed",
          "duration_ms": 2
        },
        {
          "name": "parse should handle unicode",
          "status": "failed",
          "duration_ms": 3,
          "error": {
            "expected": "こんにちは",
            "received": "???????"
          }
        }
      ]
    }
  ],
  "summary": {
    "passed": 6,
    "failed": 1,
    "skipped": 0,
    "total": 7,
    "duration_ms": 14
  }
}
```

## Test File Format

```simple
"""
Tests for JSON module
"""

import spec.{describe, it, expect, before_each, after_each}
import core.json

describe "JSON.parse":
    before_each:
        # Setup code

    it "should handle empty object":
        let result = json.parse("{}")
        expect(result).to_be_ok()
        expect(result.unwrap()).to_equal({})

    it "should handle arrays":
        let result = json.parse("[1, 2, 3]")
        expect(result.unwrap()).to_equal([1, 2, 3])

describe "JSON.stringify":
    it "should format objects":
        let obj = {"name": "test"}
        expect(json.stringify(obj)).to_equal('{"name":"test"}')
```

## Implementation Notes

1. Discover test files: `*_spec.spl`, `*_test.spl`
2. Parse spec DSL (describe, it, expect)
3. Run each test, capture output and timing
4. Format results with colors (if terminal)
5. Calculate summary statistics
6. Return exit code (0 = pass, 1 = fail)

### Important Current Caveats

Interpreter-mode test execution still has limitations in this repo. Some remote
hardware specs are therefore used primarily to verify loading, helper wiring,
and command construction until the relevant backend session is actually
available.

The current Rust `bin/simple test` entrypoint also only accepts
`interpreter|smf|native` as explicit execution modes. Composite remote forms
like `interpreter(remote(baremetal(riscv32)))` are currently rejected with a
warning and then executed as plain interpreter mode. Until that is fixed, the
documented composite mode string should be treated as the intended interface,
not a verified current behavior.

## Watch Mode

```bash
$ simple_test --watch

Watching for changes...

[15:42:01] Running tests...
Tests: 7 passed, 0 failed

[15:42:15] File changed: src/compiler_core/json.spl
[15:42:15] Running tests...
Tests: 6 passed, 1 failed
```

## Dependencies

- `native_fs_read_string` - File reading
- `sys_get_args` - Command-line arguments
- File watcher (for --watch mode)

## Exit Codes

| Code | Meaning |
|------|---------|
| 0 | All tests passed |
| 1 | Some tests failed |
| 2 | Error (file not found, parse error) |
